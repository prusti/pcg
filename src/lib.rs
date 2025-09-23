// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

/* Depending on the client's rust version, some of the features below
may already be stabilized */

#![allow(stable_features)]
#![feature(trait_alias)]
#![feature(associated_type_defaults)]
#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(if_let_guard)]
#![feature(never_type)]
#![feature(proc_macro_hygiene)]
#![feature(anonymous_lifetime_in_impl_trait)]
#![feature(stmt_expr_attributes)]
#![feature(allocator_api)]
#![feature(let_chains)]

pub mod action;
pub mod borrow_checker;
pub mod borrow_pcg;
pub mod coupling;
pub mod error;
pub mod r#loop;
pub mod owned_pcg;
use std::{borrow::Cow, path::PathBuf};

#[deprecated(note = "Use `owned_pcg` instead")]
pub use owned_pcg as free_pcs;
pub mod pcg;
pub mod results;
pub mod rustc_interface;
pub mod utils;
#[cfg(feature = "visualization")]
pub mod visualization;

use action::PcgActions;
use borrow_checker::BorrowCheckerInterface;
use borrow_pcg::graph::borrows_imgcat_debug;
use pcg::{CapabilityKind, PcgEngine, PcgSuccessor};
use rustc_interface::{
    borrowck::{self, BorrowSet, LocationTable, PoloniusInput, RegionInferenceContext},
    dataflow::{AnalysisEngine, compute_fixpoint},
    middle::{
        mir::{self, Body},
        ty::{self, TyCtxt},
    },
    mir_dataflow::move_paths::MoveData,
    span::def_id::LocalDefId,
};
use serde_json::json;
use utils::{
    CompilerCtxt, Place, VALIDITY_CHECKS, VALIDITY_CHECKS_WARN_ONLY,
    display::{DebugLines, DisplayWithCompilerCtxt},
    validity::HasValidityCheck,
};

#[cfg(feature = "visualization")]
use visualization::mir_graph::generate_json_from_mir;

use utils::json::ToJsonWithCompilerCtxt;

/// The result of the PCG analysis.
pub type PcgOutput<'a, 'tcx> = results::PcgAnalysisResults<'a, 'tcx>;
/// Instructs that the current capability to the place (first [`CapabilityKind`]) should
/// be weakened to the second given capability. We guarantee that `_.1 > _.2`.
/// If `_.2` is `None`, the capability is removed.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Weaken<'tcx> {
    pub(crate) place: Place<'tcx>,
    pub(crate) from: CapabilityKind,
    pub(crate) to: Option<CapabilityKind>,
}

impl<'tcx> Weaken<'tcx> {
    pub(crate) fn debug_line<BC: Copy>(&self, ctxt: CompilerCtxt<'_, 'tcx, BC>) -> String {
        let to_str = match self.to {
            Some(to) => format!("{to:?}"),
            None => "None".to_string(),
        };
        format!(
            "Weaken {} from {:?} to {}",
            self.place.to_short_string(ctxt),
            self.from,
            to_str
        )
    }

    pub(crate) fn new<'a>(
        place: Place<'tcx>,
        from: CapabilityKind,
        to: Option<CapabilityKind>,
        _ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Self
    where
        'tcx: 'a,
    {
        // TODO: Sometimes R can be downgraded to W
        // if let Some(to) = to {
        //     pcg_validity_assert!(
        //         from > to,
        //         "Weak of ({}: {}): FROM capability ({:?}) is not greater than TO capability ({:?})",
        //         place.to_short_string(ctxt),
        //         place.ty(ctxt).ty,
        //         from,
        //         to
        //     );
        // }
        Self { place, from, to }
    }

    pub fn place(&self) -> Place<'tcx> {
        self.place
    }

    pub fn from_cap(&self) -> CapabilityKind {
        self.from
    }

    pub fn to_cap(&self) -> Option<CapabilityKind> {
        self.to
    }
}

/// Instructs that the capability to the place should be restored to the
/// given capability, e.g. after a borrow expires, the borrowed place should be
/// restored to exclusive capability.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct RestoreCapability<'tcx> {
    place: Place<'tcx>,
    capability: CapabilityKind,
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> ToJsonWithCtxt<Ctxt>
    for RestoreCapability<'tcx>
{
    fn to_json(&self, ctxt: Ctxt) -> serde_json::Value {
        json!({
            "place": self.place.to_json(ctxt.ctxt()),
            "capability": format!("{:?}", self.capability),
        })
    }
}
impl<'tcx> RestoreCapability<'tcx> {
    pub(crate) fn debug_line<BC: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, BC>) -> String {
        format!(
            "Restore {} to {:?}",
            self.place.to_short_string(repacker),
            self.capability,
        )
    }

    pub(crate) fn new(place: Place<'tcx>, capability: CapabilityKind) -> Self {
        Self { place, capability }
    }

    pub fn place(&self) -> Place<'tcx> {
        self.place
    }

    pub fn capability(&self) -> CapabilityKind {
        self.capability
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> ToJsonWithCtxt<Ctxt> for Weaken<'tcx> {
    fn to_json(&self, repacker: Ctxt) -> serde_json::Value {
        json!({
            "place": self.place.to_json(repacker.ctxt()),
            "old": format!("{:?}", self.from),
            "new": format!("{:?}", self.to),
        })
    }
}

impl<'tcx> DebugLines<CompilerCtxt<'_, 'tcx>> for BorrowPcgActions<'tcx> {
    fn debug_lines(&self, repacker: CompilerCtxt<'_, 'tcx>) -> Vec<String> {
        self.0
            .iter()
            .map(|action| action.debug_line(repacker))
            .collect()
    }
}

use borrow_pcg::action::actions::BorrowPcgActions;
use utils::eval_stmt_data::EvalStmtData;

struct PCGStmtVisualizationData<'a, 'tcx> {
    actions: &'a EvalStmtData<PcgActions<'tcx>>,
}

struct PcgSuccessorVisualizationData<'a, 'tcx> {
    actions: &'a PcgActions<'tcx>,
}

impl<'tcx, 'a> From<&'a PcgSuccessor<'a, 'tcx>> for PcgSuccessorVisualizationData<'a, 'tcx> {
    fn from(successor: &'a PcgSuccessor<'a, 'tcx>) -> Self {
        Self {
            actions: &successor.actions,
        }
    }
}

impl<'a, 'tcx, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> ToJsonWithCtxt<Ctxt>
    for PcgSuccessorVisualizationData<'a, 'tcx>
{
    fn to_json(&self, repacker: Ctxt) -> serde_json::Value {
        json!({
            "actions": self.actions.iter().map(|a| a.to_json(repacker)).collect::<Vec<_>>(),
        })
    }
}

impl<'a, 'tcx, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> ToJsonWithCtxt<Ctxt>
    for PCGStmtVisualizationData<'a, 'tcx>
{
    fn to_json(&self, repacker: Ctxt) -> serde_json::Value {
        json!({
            "actions": self.actions.to_json(repacker),
        })
    }
}

impl<'a, 'tcx> PCGStmtVisualizationData<'a, 'tcx> {
    fn new<'mir>(location: &'a PcgLocation<'a, 'tcx>) -> Self
    where
        'tcx: 'mir,
    {
        Self {
            actions: &location.actions,
        }
    }
}

/// Exposes accessors to the body and borrow-checker data for a MIR function.
/// Types that implement this trait are used as inputs to the PCG.
///
/// Note that [`borrowck::BodyWithBorrowckFacts`] from the Rust compiler implements this trait.
pub trait BodyAndBorrows<'tcx> {
    fn body(&self) -> &Body<'tcx>;
    fn borrow_set(&self) -> &BorrowSet<'tcx>;
    fn region_inference_context(&self) -> &RegionInferenceContext<'tcx>;
    fn location_table(&self) -> &LocationTable;
    fn input_facts(&self) -> &PoloniusInput;
}

impl<'tcx> BodyAndBorrows<'tcx> for borrowck::BodyWithBorrowckFacts<'tcx> {
    fn body(&self) -> &Body<'tcx> {
        &self.body
    }
    fn borrow_set(&self) -> &BorrowSet<'tcx> {
        &self.borrow_set
    }
    fn region_inference_context(&self) -> &RegionInferenceContext<'tcx> {
        &self.region_inference_context
    }

    fn location_table(&self) -> &LocationTable {
        self.location_table.as_ref().unwrap()
    }

    fn input_facts(&self) -> &PoloniusInput {
        self.input_facts.as_ref().unwrap()
    }
}

pub struct PcgCtxtCreator<'tcx> {
    tcx: TyCtxt<'tcx>,
    arena: bumpalo::Bump,
    settings: PcgSettings,
    debug_visualization_identifiers: Vec<String>,
}

impl<'tcx> PcgCtxtCreator<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            arena: bumpalo::Bump::new(),
            debug_visualization_identifiers: vec![],
            settings: PcgSettings::new(),
        }
    }

    fn alloc<'a, T: 'a>(&'a self, val: T) -> &'a T {
        self.arena.alloc(val)
    }

    pub fn new_ctxt<'slf: 'a, 'a>(
        &'slf mut self,
        body: &'a impl BodyAndBorrows<'tcx>,
        bc: &'a impl BorrowCheckerInterface<'tcx>,
    ) -> &'a PcgCtxt<'a, 'tcx> {
        let pcg_ctxt: PcgCtxt<'a, 'tcx> =
            PcgCtxt::with_settings(body.body(), self.tcx, bc, Cow::Borrowed(&self.settings));
        if let Some(identifier) = pcg_ctxt.visualization_output_identifier() {
            self.debug_visualization_identifiers.push(identifier);
        }
        self.alloc(pcg_ctxt)
    }

    pub fn new_nll_ctxt<'slf: 'a, 'a>(
        &'slf mut self,
        body: &'a impl BodyAndBorrows<'tcx>,
    ) -> &'a PcgCtxt<'a, 'tcx> {
        let bc = self.arena.alloc(NllBorrowCheckerImpl::new(self.tcx, body));
        let pcg_ctxt: PcgCtxt<'a, 'tcx> =
            PcgCtxt::with_settings(body.body(), self.tcx, bc, Cow::Borrowed(&self.settings));
        if let Some(identifier) = pcg_ctxt.visualization_output_identifier() {
            self.debug_visualization_identifiers.push(identifier);
        }
        self.alloc(pcg_ctxt)
    }

    pub(crate) fn write_debug_visualization_metadata(self) {
        if !self.debug_visualization_identifiers.is_empty() {
            self.settings
                .write_debug_visualization_metadata(&self.debug_visualization_identifiers);
        }
    }
}

pub struct PcgCtxt<'a, 'tcx> {
    compiler_ctxt: CompilerCtxt<'a, 'tcx>,
    move_data: MoveData<'tcx>,
    settings: Cow<'a, PcgSettings>,
    pub(crate) arena: bumpalo::Bump,
}

impl<'a, 'mir: 'a, 'tcx: 'mir>
    HasBorrowCheckerCtxt<'mir, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for &'a PcgCtxt<'mir, 'tcx>
{
    fn bc_ctxt(&self) -> CompilerCtxt<'mir, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>> {
        self.compiler_ctxt
    }

    fn bc(&self) -> &'a dyn BorrowCheckerInterface<'tcx> {
        self.compiler_ctxt.bc()
    }
}

impl<'mir, 'tcx> HasCompilerCtxt<'mir, 'tcx> for &PcgCtxt<'mir, 'tcx> {
    fn ctxt(&self) -> CompilerCtxt<'mir, 'tcx, ()> {
        CompilerCtxt::new(self.compiler_ctxt.mir, self.compiler_ctxt.tcx, ())
    }
}

impl<'a, 'mir, 'tcx> HasSettings<'a> for &'a PcgCtxt<'mir, 'tcx> {
    fn settings(&self) -> &'a PcgSettings {
        &self.settings
    }
}

fn gather_moves<'tcx>(body: &Body<'tcx>, tcx: ty::TyCtxt<'tcx>) -> MoveData<'tcx> {
    MoveData::gather_moves(body, tcx, |_| true)
}

impl<'a, 'tcx> PcgCtxt<'a, 'tcx> {
    pub fn new<BC: BorrowCheckerInterface<'tcx> + ?Sized>(
        body: &'a Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        bc: &'a BC,
    ) -> Self {
        Self::with_settings(body, tcx, bc, Cow::Owned(PcgSettings::new()))
    }

    pub fn with_settings<BC: BorrowCheckerInterface<'tcx> + ?Sized>(
        body: &'a Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        bc: &'a BC,
        settings: Cow<'a, PcgSettings>,
    ) -> Self {
        let ctxt = CompilerCtxt::new(body, tcx, bc.as_dyn());
        Self {
            compiler_ctxt: ctxt,
            move_data: gather_moves(ctxt.body(), ctxt.tcx()),
            settings,
            arena: bumpalo::Bump::new(),
        }
    }

    pub fn update_debug_visualization_metadata(&self) {
        eprintln!("Updating debug visualization metadata");
        if let Some(identifier) = self.visualization_output_identifier() {
            eprintln!(
                "Writing new debug visualization metadata for {}",
                identifier
            );
            self.settings
                .write_new_debug_visualization_metadata(&identifier);
        }
    }

    pub fn body_def_id(&self) -> LocalDefId {
        self.compiler_ctxt.def_id()
    }

    pub(crate) fn visualization_output_identifier(&self) -> Option<String> {
        if self.settings.visualization {
            Some(
                self.compiler_ctxt
                    .tcx()
                    .def_path_str(self.compiler_ctxt.def_id()),
            )
        } else {
            None
        }
    }

    pub(crate) fn visualization_output_path(&self) -> Option<PathBuf> {
        if self.settings.visualization {
            Some(
                self.settings
                    .visualization_data_dir
                    .join(self.visualization_output_identifier()?),
            )
        } else {
            None
        }
    }
}

/// The main entrypoint for running the PCG.
///
/// # Arguments
///
/// * `pcg_ctxt` - The context the PCG will use for its analysis. Use [`PcgCtxt::new`] to create this.
pub fn run_pcg<'a, 'tcx>(pcg_ctxt: &'a PcgCtxt<'_, 'tcx>) -> PcgOutput<'a, 'tcx> {
    let engine = PcgEngine::new(
        pcg_ctxt.compiler_ctxt,
        &pcg_ctxt.move_data,
        &pcg_ctxt.arena,
        pcg_ctxt.visualization_output_path(),
    );
    let body = pcg_ctxt.compiler_ctxt.body();
    let tcx = pcg_ctxt.compiler_ctxt.tcx();
    let mut analysis = compute_fixpoint(AnalysisEngine(engine), tcx, body);
    for block in body.basic_blocks.indices() {
        let engine = analysis.get_analysis();
        let ctxt = engine.analysis_ctxt(block);
        let state = analysis.entry_state_for_block_mut(block);
        state.complete(ctxt);
    }
    if let Some(dir_path) = &pcg_ctxt.visualization_output_path() {
        for block in body.basic_blocks.indices() {
            let state = analysis.entry_set_for_block(block);
            if state.is_bottom() {
                continue;
            }
            let block_iterations_json_file =
                dir_path.join(format!("block_{}_iterations.json", block.index()));
            let ctxt = analysis.get_analysis().analysis_ctxt(block);
            if let Some(graphs) = ctxt.graphs {
                graphs
                    .dot_graphs
                    .borrow()
                    .write_json_file(&block_iterations_json_file);
            }
        }
    }
    let mut analysis_results = results::PcgAnalysisResults::new(analysis.into_results_cursor(body));

    if validity_checks_enabled() {
        for (block, _data) in body.basic_blocks.iter_enumerated() {
            let pcs_block_option = if let Ok(opt) = analysis_results.get_all_for_bb(block) {
                opt
            } else {
                continue;
            };
            if pcs_block_option.is_none() {
                continue;
            }
            let pcs_block = pcs_block_option.unwrap();
            for (statement_index, statement) in pcs_block.statements.iter().enumerate() {
                statement.assert_validity_at_location(
                    mir::Location {
                        block,
                        statement_index,
                    },
                    pcg_ctxt,
                );
            }
        }
    }

    #[cfg(feature = "visualization")]
    if let Some(dir_path) = pcg_ctxt.visualization_output_path() {
        let edge_legend_file_path = dir_path.join("edge_legend.dot");
        let edge_legend_graph = crate::visualization::legend::generate_edge_legend().unwrap();
        std::fs::write(&edge_legend_file_path, edge_legend_graph)
            .expect("Failed to write edge legend");

        let node_legend_file_path = dir_path.join("node_legend.dot");
        let node_legend_graph = crate::visualization::legend::generate_node_legend().unwrap();
        std::fs::write(&node_legend_file_path, node_legend_graph)
            .expect("Failed to write node legend");
        generate_json_from_mir(&dir_path.join("mir.json"), pcg_ctxt.compiler_ctxt)
            .expect("Failed to generate JSON from MIR");

        // Iterate over each statement in the MIR
        for (block, _data) in body.basic_blocks.iter_enumerated() {
            let pcs_block_option = if let Ok(opt) = analysis_results.get_all_for_bb(block) {
                opt
            } else {
                continue;
            };
            if pcs_block_option.is_none() {
                continue;
            }
            let pcs_block = pcs_block_option.unwrap();
            for (statement_index, statement) in pcs_block.statements.iter().enumerate() {
                let data = PCGStmtVisualizationData::new(statement);
                let pcg_data_file_path = dir_path.join(format!(
                    "block_{}_stmt_{}_pcg_data.json",
                    block.index(),
                    statement_index
                ));
                let pcg_data_json = data.to_json(pcg_ctxt.compiler_ctxt);
                std::fs::write(&pcg_data_file_path, pcg_data_json.to_string())
                    .expect("Failed to write pcg data to JSON file");
            }
            for succ in pcs_block.terminator.succs {
                let data = PcgSuccessorVisualizationData::from(&succ);
                let pcg_data_file_path = dir_path.join(format!(
                    "block_{}_term_block_{}_pcg_data.json",
                    block.index(),
                    succ.block().index()
                ));
                let pcg_data_json = data.to_json(pcg_ctxt.compiler_ctxt);
                std::fs::write(&pcg_data_file_path, pcg_data_json.to_string())
                    .expect("Failed to write pcg data to JSON file");
            }
        }
    }

    analysis_results
}

macro_rules! pcg_validity_expect_some {
    ($cond:expr, fallback: $fallback:expr, [$($ctxt_and_loc:tt)*], $($arg:tt)*) => {
        {
            if $crate::validity_checks_enabled() {
                pcg_validity_assert!($cond.is_some(), [$($ctxt_and_loc)*], $($arg)*);
            }
            $cond.unwrap_or($fallback)
        }
    };
    ($cond:expr, fallback: $fallback:expr, $($arg:tt)*) => {
        {
            if $crate::validity_checks_enabled() {
                pcg_validity_assert!($cond.is_some(), $($arg)*);
            }
            $cond.unwrap_or($fallback)
        }
    };

    ($cond:expr, [$($ctxt_and_loc:tt)*], $($arg:tt)*) => {
        {
            if $crate::validity_checks_enabled() {
                pcg_validity_assert!($cond.is_some(), [$($ctxt_and_loc)*], $($arg)*);
            }
            $cond.expect("pcg_validity_expect_some failed")
        }
    };
    ($cond:expr, $($arg:tt)*) => {
        {
            if $crate::validity_checks_enabled() {
                pcg_validity_assert!($cond.is_some(), $($arg)*);
            }
            $cond.expect("pcg_validity_expect_some failed")
        }
    };
}

macro_rules! pcg_validity_expect_ok {
    ($cond:expr, fallback: $fallback:expr, [$($ctxt_and_loc:tt)*], $($arg:tt)*) => {
        {
            let result = $cond;
            if $crate::validity_checks_enabled() {
                pcg_validity_assert!(result.is_ok(), [$($ctxt_and_loc)*], "{}: {:?}", format!($($arg)*), result.as_ref().err());
            }
            result.unwrap_or($fallback)
        }
    };
    ($cond:expr, fallback: $fallback:expr, [$($ctxt_and_loc:tt)*]) => {
        {
            let result = $cond;
            if $crate::validity_checks_enabled() {
                pcg_validity_assert!(result.is_ok(), [$($ctxt_and_loc)*], "{}", result.as_ref().err().unwrap() );
            }
            result.unwrap_or($fallback)
        }
    };
    ($cond:expr, fallback: $fallback:expr, $($arg:tt)*) => {
        {
            let result = $cond;
            if $crate::validity_checks_enabled() {
                pcg_validity_assert!(result.is_ok(), "{}: {:?}", format!($($arg)*), result.as_ref().err());
            }
            result.unwrap_or($fallback)
        }
    };

    ($cond:expr, [$($ctxt_and_loc:tt)*], $($arg:tt)*) => {
        {
            let result = $cond;
            if $crate::validity_checks_enabled() {
                pcg_validity_assert!(result.is_ok(), [$($ctxt_and_loc)*], "{}: {:?}", format!($($arg)*), result.as_ref().err());
            }
            result.expect("pcg_validity_expect_ok failed")
        }
    };
    ($cond:expr, $($arg:tt)*) => {
        {
            let result = $cond;
            if $crate::validity_checks_enabled() {
                pcg_validity_assert!(result.is_ok(), "{}: {:?}", format!($($arg)*), result.as_ref().err());
            }
            result.expect("pcg_validity_expect_ok failed")
        }
    };
}

macro_rules! pcg_validity_assert {
    // Entry point with brackets - parse using token trees
    ($cond:expr, [$($ctxt_and_loc:tt)*]) => {
        pcg_validity_assert!(@parse_context $cond, [$($ctxt_and_loc)*], "{}", stringify!($cond))
    };
    ($cond:expr, [$($ctxt_and_loc:tt)*], $($arg:tt)*) => {
        pcg_validity_assert!(@parse_context $cond, [$($ctxt_and_loc)*], $($arg)*)
    };

    // Parse context patterns - match the entire token sequence
    (@parse_context $cond:expr, [$ctxt:tt at $loc:tt], $($arg:tt)*) => {
        {
            let ctxt = $ctxt;
            let loc = $loc;
            let func_name = ctxt.tcx().def_path_str(ctxt.body().source.def_id());
            let crate_part = std::env::var("CARGO_CRATE_NAME").map(|s| format!(" (Crate: {})", s)).unwrap_or_default();
            pcg_validity_assert!(@with_test_case $cond, ctxt, func_name, "PCG Assertion Failed {crate_part}: [{func_name} at {loc:?}] {}", format!($($arg)*));
        }
    };
    (@parse_context $cond:expr, [$ctxt:tt], $($arg:tt)*) => {
        {
            let ctxt = $ctxt;
            let func_name = ctxt.tcx().def_path_str(ctxt.body().source.def_id());
            let crate_part = std::env::var("CARGO_CRATE_NAME").map(|s| format!(" (Crate: {})", s)).unwrap_or_default();
            pcg_validity_assert!(@with_test_case $cond, ctxt, func_name, "PCG Assertion Failed {crate_part}: [{func_name}] {}", format!($($arg)*));
        }
    };

    // Helper branch that generates test case format when context is available
    (@with_test_case $cond:expr, $ctxt:expr, $func_name:expr, $($arg:tt)*) => {
        if $crate::validity_checks_enabled() {
            #[allow(clippy::neg_cmp_op_on_partial_ord)]
            if !$cond {
                tracing::error!($($arg)*);
                // Generate test case format if we're in a crate
                if let Ok(crate_name) = std::env::var("CARGO_CRATE_NAME") {
                    let crate_version = std::env::var("CARGO_PKG_VERSION").unwrap_or_else(|_| "unknown".to_string());
                    let num_bbs = $ctxt.body().basic_blocks.len();
                    let test_case = format!("{};{};2025-03-13;{};{}",
                        crate_name, crate_version, $func_name, num_bbs);
                    tracing::error!("To reproduce this failure, use test case: {}", test_case);
                }
                if !$crate::validity_checks_warn_only() {
                    assert!($cond, $($arg)*);
                }
            }
        }
    };

    // Without brackets
    ($cond:expr) => {
        pcg_validity_assert!($cond, "PCG Assertion Failed: {}", stringify!($cond))
    };
    ($cond:expr, $($arg:tt)*) => {
        if $crate::validity_checks_enabled() {
            #[allow(clippy::neg_cmp_op_on_partial_ord)]
            if !$cond {
                tracing::error!($($arg)*);
                if !$crate::validity_checks_warn_only() {
                    assert!($cond, $($arg)*);
                }
            }
        }
    };
}

pub(crate) use pcg_validity_assert;
pub(crate) use pcg_validity_expect_ok;
pub(crate) use pcg_validity_expect_some;

use crate::{
    borrow_checker::r#impl::NllBorrowCheckerImpl,
    pcg::ctxt::HasSettings,
    results::PcgLocation,
    utils::{HasBorrowCheckerCtxt, HasCompilerCtxt, PcgSettings, json::ToJsonWithCtxt},
};

pub(crate) fn validity_checks_enabled() -> bool {
    *VALIDITY_CHECKS
}

pub(crate) fn validity_checks_warn_only() -> bool {
    *VALIDITY_CHECKS_WARN_ONLY
}
