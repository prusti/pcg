// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{borrow::Cow, collections::HashMap};

use derive_more::Deref;

use crate::{
    action::{AppliedActions, BorrowPcgAction, OwnedPcgAction, PcgActions},
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeRef},
        region_projection::PlaceOrConst,
    },
    error::PcgError,
    r#loop::{PlaceUsageType, PlaceUsages},
    pcg::{
        CapabilityKind, EvalStmtPhase, Pcg, PcgEngine, PcgNode, PcgSuccessor, ctxt::HasSettings,
        place_capabilities::PlaceCapabilitiesReader, successor_blocks,
    },
    rustc_interface::{
        data_structures::fx::FxHashSet,
        dataflow::AnalysisEngine,
        index::IndexVec,
        middle::{
            mir::{self, BasicBlock, Body, Location},
            ty::TyCtxt,
        },
        mir_dataflow::ResultsCursor,
    },
    utils::{
        HasBorrowCheckerCtxt, HasCompilerCtxt, Place, display::DebugLines,
        domain_data::DomainDataStates, validity::HasValidityCheck,
    },
};

use crate::{
    borrow_pcg::action::actions::BorrowPcgActions,
    owned_pcg::RepackOp,
    utils::{CompilerCtxt, eval_stmt_data::EvalStmtData},
};

type Cursor<'mir, 'tcx, E> = ResultsCursor<'mir, 'tcx, E>;
/// The result of the PCG analysis.
pub struct PcgAnalysisResults<'a, 'tcx: 'a> {
    pub cursor: Cursor<'a, 'tcx, AnalysisEngine<PcgEngine<'a, 'tcx>>>,
    curr_stmt: Option<Location>,
    end_stmt: Option<Location>,
}

impl<'a, 'tcx: 'a> PcgAnalysisResults<'a, 'tcx> {
    pub(crate) fn new(cursor: Cursor<'a, 'tcx, AnalysisEngine<PcgEngine<'a, 'tcx>>>) -> Self {
        Self {
            cursor,
            curr_stmt: None,
            end_stmt: None,
        }
    }

    pub(crate) fn analysis_for_bb(&mut self, block: BasicBlock) {
        self.cursor.seek_to_block_start(block);
        let end_stmt = self.body().terminator_loc(block).successor_within_block();
        self.curr_stmt = Some(Location {
            block,
            statement_index: 0,
        });
        self.end_stmt = Some(end_stmt);
    }

    pub fn loop_place_usages(&self, loop_head: BasicBlock) -> Option<&PlaceUsages<'tcx>> {
        self.analysis()
            .body_analysis
            .loop_place_usage_analysis
            .get_used_places(loop_head)
    }

    fn body(&self) -> &'a Body<'tcx> {
        self.ctxt().body()
    }

    pub fn ctxt(&self) -> CompilerCtxt<'a, 'tcx> {
        self.cursor.analysis().0.ctxt
    }

    /// Returns the free pcs for the location `exp_loc` and iterates the cursor
    /// to the *end* of that location.
    ///
    /// This function may return `None` if the PCG did not analyze this block.
    /// This could happen, for example, if the block would only be reached when unwinding from a panic.
    fn next(&mut self, exp_loc: Location) -> Result<Option<PcgLocation<'a, 'tcx>>, PcgError> {
        let location = self.curr_stmt.unwrap();
        assert_eq!(location, exp_loc);
        assert!(location < self.end_stmt.unwrap());

        self.cursor.seek_after_primary_effect(location);

        let state = self.cursor.get().expect_results_or_error()?;

        let result = PcgLocation {
            location,
            actions: state.data.actions.clone(),
            states: state.data.pcg.states.to_owned(),
        };

        self.curr_stmt = Some(location.successor_within_block());

        Ok(Some(result))
    }
    pub(crate) fn terminator<'slf>(&'slf mut self) -> Result<PcgTerminator<'a, 'tcx>, PcgError> {
        let location = self.curr_stmt.unwrap();
        assert!(location == self.end_stmt.unwrap());
        self.curr_stmt = None;
        self.end_stmt = None;

        let state = self.cursor.get().expect_results_or_error()?;
        let from_pcg = &state.data.pcg;
        let from_post_main = from_pcg.states[EvalStmtPhase::PostMain].clone();
        let self_abstraction_edges = from_post_main
            .borrow
            .graph()
            .abstraction_edges()
            .collect::<FxHashSet<_>>();

        let ctxt: CompilerCtxt = self.ctxt();
        let block = &self.body()[location.block];

        let succ_blocks = successor_blocks(block.terminator())
            .into_iter()
            .filter(|succ| {
                self.cursor
                    .analysis()
                    .0
                    .reachable_blocks
                    .contains(succ.index())
            })
            .collect::<Vec<_>>();
        let succs = succ_blocks
            .into_iter()
            .map(|succ| {
                self.cursor.seek_to_block_start(succ);
                let to = self
                    .cursor
                    .get()
                    .expect_results_or_error()?
                    .data
                    .pcg
                    .clone();

                let owned_bridge = from_post_main
                    .bridge(&to.entry_state, location.block, succ, ctxt)
                    .unwrap();

                let mut borrow_actions = BorrowPcgActions::new();
                for abstraction in to.entry_state.borrow.graph().abstraction_edges() {
                    if !self_abstraction_edges.contains(&abstraction) {
                        borrow_actions.push(
                            BorrowPcgAction::add_edge(
                                BorrowPcgEdge::new(
                                    abstraction.value.clone().into(),
                                    abstraction.conditions,
                                ),
                                "terminator",
                                ctxt,
                            ),
                            ctxt,
                        );
                    }
                }

                let mut actions: PcgActions<'tcx> = PcgActions::new(
                    owned_bridge
                        .into_iter()
                        .map(|r| OwnedPcgAction::new(r, None).into())
                        .collect(),
                );
                actions.extend(borrow_actions.into());

                Ok(PcgSuccessor::new(
                    succ,
                    actions,
                    to.entry_state.borrow.clone().into(),
                ))
            })
            .collect::<Result<Vec<_>, PcgError>>()?;
        Ok(PcgTerminator { succs })
    }

    /// Obtains the results of the dataflow analysis for all blocks.
    ///
    /// This is rather expensive to compute and may take a lot of memory. You
    /// may want to consider using `get_all_for_bb` instead.
    pub fn results_for_all_blocks(&mut self) -> Result<PcgBasicBlocks<'a, 'tcx>, PcgError> {
        let mut result = IndexVec::new();
        for block in self.body().basic_blocks.indices() {
            let pcg_block = self.get_all_for_bb(block)?;
            result.push(pcg_block);
        }
        Ok(PcgBasicBlocks(result))
    }

    pub fn analysis(&self) -> &PcgEngine<'a, 'tcx> {
        &self.cursor.analysis().0
    }

    pub fn first_error(&self) -> Option<PcgError> {
        self.analysis().first_error.error().cloned()
    }

    /// Recommended interface.
    /// Does *not* require that one calls `analysis_for_bb` first
    /// This function may return `None` if the PCG did not analyze this block.
    /// This could happen, for example, if the block would only be reached when unwinding from a panic.
    pub fn get_all_for_bb<'slf>(
        &'slf mut self,
        block: BasicBlock,
    ) -> Result<Option<PcgBasicBlock<'a, 'tcx>>, PcgError> {
        if !self.analysis().reachable_blocks.contains(block.index()) {
            return Ok(None);
        }
        self.analysis_for_bb(block);
        let mut statements: Vec<PcgLocation<'a, 'tcx>> = Vec::new();
        let end_stmt = self.end_stmt.unwrap();
        while self.curr_stmt.unwrap() != end_stmt {
            let stmt = self.next(self.curr_stmt.unwrap())?;
            if let Some(stmt) = stmt {
                statements.push(stmt);
            } else {
                return Ok(None);
            }
        }
        let terminator = self.terminator()?;
        Ok(Some(PcgBasicBlock {
            statements,
            terminator,
            block,
        }))
    }
}

/// The results of the PCG analysis for all basic blocks.
#[derive(Deref)]
pub struct PcgBasicBlocks<'a, 'tcx>(IndexVec<BasicBlock, Option<PcgBasicBlock<'a, 'tcx>>>);

impl<'tcx> PcgBasicBlocks<'_, 'tcx> {
    pub fn get_statement(&self, location: Location) -> Option<&PcgLocation<'_, 'tcx>> {
        if let Some(pcg_block) = &self.0[location.block] {
            pcg_block.statements.get(location.statement_index)
        } else {
            None
        }
    }

    fn aggregate<T: std::hash::Hash + std::cmp::Eq>(
        &self,
        f: impl Fn(&PcgLocation<'_, 'tcx>) -> FxHashSet<T>,
    ) -> FxHashSet<T> {
        let mut result = FxHashSet::default();
        for block in self.0.iter() {
            if let Some(pcg_block) = &block {
                for stmt in pcg_block.statements.iter() {
                    result.extend(f(stmt));
                }
            }
        }
        result
    }

    pub fn all_place_aliases<'mir>(
        &self,
        place: mir::Place<'tcx>,
        body: &'mir Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> FxHashSet<mir::Place<'tcx>> {
        self.aggregate(|stmt| stmt.aliases(place, body, tcx))
    }
}

/// The results of the PCG analysis for a basic block.
pub struct PcgBasicBlock<'a, 'tcx> {
    pub statements: Vec<PcgLocation<'a, 'tcx>>,
    pub terminator: PcgTerminator<'a, 'tcx>,
    pub(crate) block: BasicBlock,
}

impl<'tcx> PcgBasicBlock<'_, 'tcx> {
    pub fn loop_invariant_place_capabilities(
        &self,
        place_usages: &PlaceUsages<'tcx>,
        ctxt: impl HasCompilerCtxt<'_, 'tcx>,
    ) -> HashMap<Place<'tcx>, CapabilityKind> {
        let initial_capabilities =
            self.statements[0].states[EvalStmtPhase::PreOperands].capabilities();
        let mut result = HashMap::default();
        for place_usage in place_usages.iter() {
            if let Some(initial_capability) = initial_capabilities.get(place_usage.place, ctxt) {
                let usage_capability = match place_usage.usage {
                    PlaceUsageType::Read => CapabilityKind::Read,
                    PlaceUsageType::Mutate => CapabilityKind::Exclusive,
                };
                if let Some(joined_capability) = initial_capability
                    .expect_concrete()
                    .minimum(usage_capability)
                {
                    result.insert(place_usage.place, joined_capability);
                }
            }
        }
        result
    }

    pub fn debug_lines(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Vec<String> {
        let mut result = Vec::new();
        for stmt in self.statements.iter() {
            for phase in EvalStmtPhase::phases() {
                for line in stmt.debug_lines(phase, ctxt) {
                    result.push(format!("{:?} {}: {}", stmt.location, phase, line));
                }
            }
        }
        for term_succ in self.terminator.succs.iter() {
            for line in term_succ.debug_lines(ctxt) {
                result.push(format!(
                    "{:?} -> {:?}: {}",
                    self.block,
                    term_succ.block(),
                    line
                ));
            }
        }
        result
    }
}

/// The PCG state at a MIR location. Also contains associated actions performed
/// when analysing the statement at that location.
#[derive(Debug, Clone)]
pub struct PcgLocation<'a, 'tcx> {
    pub location: Location,
    pub states: DomainDataStates<Pcg<'a, 'tcx>>,
    pub(crate) actions: EvalStmtData<AppliedActions<'tcx>>,
}

impl<'tcx> DebugLines<CompilerCtxt<'_, 'tcx>> for Vec<RepackOp<'tcx>> {
    fn debug_lines(&self, _ctxt: CompilerCtxt<'_, 'tcx>) -> Vec<Cow<'static, str>> {
        self.iter().map(|r| Cow::Owned(format!("{r:?}"))).collect()
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasSettings<'a> + HasBorrowCheckerCtxt<'a, 'tcx>>
    HasValidityCheck<'a, 'tcx, Ctxt> for PcgLocation<'a, 'tcx>
{
    fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
        // TODO
        self.states.check_validity(ctxt)
    }
}

impl<'tcx> PcgLocation<'_, 'tcx> {
    pub fn actions<'slf>(&'slf self, phase: EvalStmtPhase) -> PcgActions<'tcx> {
        self.actions[phase].map_actions(|action| action.action.clone())
    }

    pub fn ancestor_edges<'slf, 'mir: 'slf, 'bc: 'slf>(
        &'slf self,
        place: Place<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> FxHashSet<BorrowPcgEdgeRef<'tcx, 'slf>> {
        let borrows_graph = self.states[EvalStmtPhase::PostMain].borrow.graph();
        let mut ancestors = borrows_graph.ancestor_edges(place.into(), ctxt);
        for rp in place.lifetime_projections(ctxt) {
            ancestors.extend(borrows_graph.ancestor_edges(rp.into(), ctxt));
        }
        ancestors
    }

    pub fn aliases<'mir>(
        &self,
        place: impl Into<Place<'tcx>>,
        body: &'mir Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> FxHashSet<mir::Place<'tcx>> {
        let place: Place<'tcx> = place.into();
        // let place = place.with_inherent_region(ctxt);
        let ctxt = CompilerCtxt::new(body, tcx, ());
        self.states[EvalStmtPhase::PostMain]
            .borrow
            .graph()
            .aliases(place.into(), ctxt)
            .into_iter()
            .flat_map(|p| match p {
                PcgNode::Place(p) => p.as_current_place(),
                PcgNode::LifetimeProjection(p) => match p.base() {
                    PlaceOrConst::Place(p) => {
                        let assoc_place = p.related_local_place();
                        if assoc_place.is_ref(ctxt) {
                            Some(assoc_place.project_deref(ctxt))
                        } else {
                            None
                        }
                    }
                    _ => None,
                },
            })
            .map(|p| p.to_rust_place(ctxt))
            .collect()
    }

    pub(crate) fn debug_lines(
        &self,
        phase: EvalStmtPhase,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Vec<Cow<'static, str>> {
        let mut result = self.states[phase].debug_lines(ctxt);
        for action in self.actions[phase].iter() {
            result.push(action.action.debug_line(ctxt));
        }
        result
    }
}

#[derive(Debug)]
pub struct PcgTerminator<'a, 'tcx> {
    pub succs: Vec<PcgSuccessor<'a, 'tcx>>,
}
