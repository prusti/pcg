use std::{
    collections::{BTreeMap, BTreeSet},
    io::Write,
    path::Path,
};

use borrowck_body_storage::{set_mir_borrowck, take_stored_body};
use pcg::utils::PcgSettings;
use pcg::{
    HasSettings, PcgCtxtCreator, PcgOutput,
    borrow_checker::r#impl::{NllBorrowCheckerImpl, PoloniusBorrowChecker},
    borrow_pcg::region_projection::{PcgRegion, RegionIdx},
    pcg::BodyWithBorrowckFacts,
    run_pcg,
    rustc_interface::{
        interface::{self, interface::Compiler},
        driver::{self, Compilation, init_rustc_env_logger},
        borrowck::{BorrowIndex, RichLocation},
        data_structures::{fx::FxHashSet, graph::is_cyclic},
        hir::{def::DefKind, def_id::LocalDefId},
        middle::{
            mir::{Body, Local, Location},
            ty::{RegionVid, TyCtxt},
        },
        span::SpanSnippetError,
        session::{EarlyDiagCtxt, config::ErrorOutputType},
    },
    utils::{
        CompilerCtxt, GlobalPcgSettings, HasCompilerCtxt, Place,
        callbacks::{RustBorrowCheckerImpl, in_cargo_crate},
    },
    visualization::bc_facts_graph::{
        region_inference_outlives, subset_anywhere, subset_at_location,
    },
};

fn hir_body_owners(tcx: TyCtxt<'_>) -> impl std::iter::Iterator<Item = LocalDefId> + '_ {
    tcx.hir_body_owners()
}

fn is_primary_crate() -> bool {
    std::env::var("CARGO_PRIMARY_PACKAGE").is_ok()
}

fn should_check_body(settings: &GlobalPcgSettings, body: &Body<'_>) -> bool {
    if settings.skip_bodies_with_loops && is_cyclic(&body.basic_blocks) {
        return false;
    }
    if let Some(len) = settings.max_basic_blocks {
        body.basic_blocks.len() <= len
    } else {
        true
    }
}

fn cargo_crate_name() -> Option<String> {
    std::env::var("CARGO_CRATE_NAME").ok()
}

pub(crate) struct PcgAsRustcCallbacks;

impl driver::Callbacks for PcgAsRustcCallbacks {
    fn config(&mut self, config: &mut interface::Config) {
        tracing::debug!("Setting mir_borrowck");
        assert!(config.override_queries.is_none());
        config.override_queries = Some(set_mir_borrowck);
        let early_dcx = EarlyDiagCtxt::new(ErrorOutputType::default());
        init_rustc_env_logger(&early_dcx);
    }

    fn after_analysis(&mut self, _compiler: &Compiler, tcx: TyCtxt<'_>) -> Compilation {
        unsafe {
            run_pcg_on_all_fns(tcx);
        }
        if in_cargo_crate() {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}

/// # Safety
/// 1. Should be called for the same `tcx` where the borrow-checking occurred.
/// 2. The `config` for the compiler run should have had `override_queries` set to [`set_mir_borrowck`].
pub unsafe fn run_pcg_on_all_fns(tcx: TyCtxt<'_>) {
    let global_settings = GlobalPcgSettings::new();
    let mut ctxt_creator = PcgCtxtCreator::new(tcx);
    let settings = ctxt_creator.settings().clone();
    tracing::info!("Running PCG on all functions");
    tracing::info!(
        "Validity checks {}",
        if settings.validity_checks {
            "enabled"
        } else {
            "disabled"
        }
    );
    if let Some(block) = settings.debug_block {
        tracing::info!("Debug block: {:?}", block);
    }
    if in_cargo_crate() && !is_primary_crate() {
        // We're running in cargo, but not compiling the primary package
        // We don't want to check dependencies, so abort
        return;
    }

    if std::env::var("PCG_TYPECHECK_ONLY")
        .unwrap_or("false".to_string())
        .parse::<bool>()
        .unwrap()
    {
        return;
    }

    for def_id in hir_body_owners(tcx) {
        let kind = tcx.def_kind(def_id);
        if !matches!(kind, DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        let item_name = tcx.def_path_str(def_id.to_def_id()).to_string();
        if let Some(ref function) = settings.check_function
            && function != &item_name
        {
            tracing::debug!(
                "Skipping function: {item_name} because PCG_CHECK_FUNCTION is set to {function}"
            );
            continue;
        }
        if let Some(ref function) = settings.skip_function
            && function == &item_name
        {
            tracing::info!(
                "Skipping function: {item_name} because PCG_SKIP_FUNCTION is set to {function}"
            );
            continue;
        }
        // Safety: Is safe provided the preconditions to `run_pcg_on_all_fns` were met.
        let body = unsafe { take_stored_body(tcx, def_id) };

        if !should_check_body(&global_settings, &body.body) {
            continue;
        }
        tracing::info!("Def Id: {:?}", def_id);

        tracing::info!(
            "{}Running PCG on function: {} with {} basic blocks",
            cargo_crate_name().map_or("".to_string(), |name| format!("{name}: ")),
            item_name,
            body.body.basic_blocks.len()
        );
        tracing::info!("Path: {:?}", body.body.span);
        tracing::debug!("Number of basic blocks: {}", body.body.basic_blocks.len());
        tracing::debug!("Number of locals: {}", body.body.local_decls.len());
        run_pcg_on_fn(&body, &mut ctxt_creator);
    }
    ctxt_creator.write_debug_visualization_metadata();
}

pub(crate) fn run_pcg_on_fn<'tcx>(
    body: &BodyWithBorrowckFacts<'tcx>,
    ctxt_creator: &mut PcgCtxtCreator<'tcx>,
) {
    let tcx = ctxt_creator.tcx;
    let region_debug_name_overrides = if let Ok(lines) = source_lines(tcx, &body.body) {
        lines
            .iter()
            .flat_map(|l| l.split("PCG_LIFETIME_DISPLAY: ").nth(1))
            .map(|l| LifetimeRenderAnnotation::from(l).to_pair(tcx, &body.body))
            .collect::<_>()
    } else {
        BTreeMap::new()
    };
    let mut bc = if ctxt_creator.settings().polonius {
        RustBorrowCheckerImpl::Polonius(PoloniusBorrowChecker::new(tcx, body))
    } else {
        RustBorrowCheckerImpl::Nll(NllBorrowCheckerImpl::new(tcx, body))
    };
    {
        let region_printer = bc.region_pretty_printer();
        for (region, name) in region_debug_name_overrides {
            region_printer.insert(region, name.to_string());
        }
    }
    let pcg_ctxt = ctxt_creator.new_ctxt(body, &bc);
    let mut output = run_pcg(pcg_ctxt);
    let ctxt = CompilerCtxt::new(&body.body, tcx, &bc);

    if let Some(dir_path) = pcg_ctxt.visualization_output_path() {
        emit_borrowcheck_graphs(&dir_path, ctxt);
    }

    emit_and_check_annotations(
        pcg_ctxt.ctxt().body_def_path_str(),
        pcg_ctxt.settings(),
        &mut output,
    );
}

fn emit_and_check_annotations(
    item_name: String,
    settings: &PcgSettings,
    output: &mut PcgOutput<'_, '_>,
) {
    let emit_pcg_annotations = settings.emit_annotations;
    let check_pcg_annotations = settings.check_annotations;

    let ctxt = output.ctxt();

    if emit_pcg_annotations || check_pcg_annotations {
        let mut debug_lines = Vec::new();

        if let Some(err) = output.first_error() {
            debug_lines.push(format!("{err:?}"));
        }
        for block in ctxt.body().basic_blocks.indices() {
            if let Ok(Some(state)) = output.get_all_for_bb(block) {
                for line in state.debug_lines(ctxt) {
                    debug_lines.push(line);
                }
            }
        }
        if emit_pcg_annotations {
            for line in debug_lines.iter() {
                eprintln!("// PCG: {line}");
            }
        }
        if check_pcg_annotations {
            if let Ok(source) = source_lines(ctxt.tcx(), ctxt.body()) {
                let debug_lines_set: FxHashSet<_> = debug_lines.into_iter().collect();
                let expected_annotations = source
                    .iter()
                    .flat_map(|l| l.split("// PCG: ").nth(1))
                    .map(|l| l.trim())
                    .collect::<Vec<_>>();
                let not_expected_annotations = source
                    .iter()
                    .flat_map(|l| l.split("// ~PCG: ").nth(1))
                    .map(|l| l.trim())
                    .collect::<Vec<_>>();
                let missing_annotations = expected_annotations
                    .iter()
                    .filter(|a| !debug_lines_set.contains(**a))
                    .collect::<Vec<_>>();
                if !missing_annotations.is_empty() {
                    panic!("Missing annotations: {missing_annotations:?}");
                }
                for not_expected_annotation in not_expected_annotations {
                    if debug_lines_set.contains(not_expected_annotation) {
                        panic!("Unexpected annotation: {not_expected_annotation}");
                    }
                }
            } else {
                tracing::warn!("No source for function: {}", item_name);
            }
        }
    }
}

fn source_lines(tcx: TyCtxt<'_>, mir: &Body<'_>) -> Result<Vec<String>, SpanSnippetError> {
    let source_map = tcx.sess.source_map();
    let span = mir.span;
    let lines = source_map.span_to_snippet(span)?;
    Ok(lines.lines().map(|l| l.to_string()).collect())
}

struct LifetimeRenderAnnotation {
    var: String,
    region_idx: RegionIdx,
    display_as: String,
}

impl LifetimeRenderAnnotation {
    fn get_place<'tcx>(&self, tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Place<'tcx> {
        if self.var.starts_with('_')
            && let Ok(idx) = self.var.split_at(1).1.parse::<usize>()
        {
            let local: Local = idx.into();
            local.into()
        } else {
            CompilerCtxt::new(body, tcx, ())
                .local_place(self.var.as_str())
                .unwrap()
        }
    }

    fn to_pair<'tcx>(&self, tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> (RegionVid, String) {
        let place = self.get_place(tcx, body);
        let region: PcgRegion = place.regions(CompilerCtxt::new(body, tcx, ()))[self.region_idx];
        (region.vid().unwrap(), self.display_as.clone())
    }
}

impl From<&str> for LifetimeRenderAnnotation {
    fn from(s: &str) -> Self {
        let parts = s.split(" ").collect::<Vec<_>>();
        Self {
            var: parts[0].to_string(),
            region_idx: parts[1].parse::<usize>().unwrap().into(),
            display_as: parts[2].to_string(),
        }
    }
}

fn emit_borrowcheck_graphs<'a, 'tcx: 'a, 'bc>(
    dir_path: &Path,
    ctxt: CompilerCtxt<'a, 'tcx, &'bc RustBorrowCheckerImpl<'a, 'tcx>>,
) {
    if let RustBorrowCheckerImpl::Polonius(ref bc) = *ctxt.bc() {
        let ctxt = CompilerCtxt::new(ctxt.body(), ctxt.tcx(), bc);
        for (block_index, data) in ctxt.body().basic_blocks.iter_enumerated() {
            let num_stmts = data.statements.len();
            for stmt_index in 0..num_stmts + 1 {
                let location = Location {
                    block: block_index,
                    statement_index: stmt_index,
                };
                let start_dot_graph = subset_at_location(location, true, ctxt);
                let start_file_path = dir_path.join(format!(
                    "bc_facts_graph_{block_index:?}_{stmt_index}_start.dot"
                ));
                start_dot_graph.write_to_file(&start_file_path).unwrap();
                let mid_dot_graph = subset_at_location(location, false, ctxt);
                let mid_file_path = dir_path.join(format!(
                    "bc_facts_graph_{block_index:?}_{stmt_index}_mid.dot"
                ));
                mid_dot_graph.write_to_file(&mid_file_path).unwrap();

                let mut bc_facts_file = std::fs::File::create(
                    dir_path.join(format!("bc_facts_{block_index:?}_{stmt_index}.txt")),
                )
                .unwrap();

                fn write_loans(
                    bc: &PoloniusBorrowChecker<'_, '_>,
                    loans: BTreeMap<RegionVid, BTreeSet<BorrowIndex>>,
                    loans_file: &mut std::fs::File,
                    _ctxt: CompilerCtxt<'_, '_, &PoloniusBorrowChecker<'_, '_>>,
                ) {
                    for (region, indices) in loans {
                        writeln!(loans_file, "Region: {region:?}").unwrap();
                        for index in indices {
                            writeln!(loans_file, "  {:?}", bc.region_of_borrow(index)).unwrap();
                        }
                    }
                }

                fn write_bc_facts(
                    bc: &PoloniusBorrowChecker<'_, '_>,
                    location: RichLocation,
                    bc_facts_file: &mut std::fs::File,
                    ctxt: CompilerCtxt<'_, '_, &PoloniusBorrowChecker<'_, '_>>,
                ) {
                    let origin_contains_loan_at = ctxt.bc().origin_contains_loan_at_map(location);
                    writeln!(bc_facts_file, "{location:?} Origin contains loan at:").unwrap();
                    if let Some(origin_contains_loan_at) = origin_contains_loan_at {
                        write_loans(bc, origin_contains_loan_at, bc_facts_file, ctxt);
                    }
                    writeln!(bc_facts_file, "{location:?} Origin live on entry:").unwrap();
                    if let Some(origin_live_on_entry) = ctxt.bc().origin_live_on_entry(location) {
                        for region in origin_live_on_entry {
                            writeln!(bc_facts_file, "  Region: {region:?}").unwrap();
                        }
                    }
                    writeln!(bc_facts_file, "{location:?} Loans live at:").unwrap();
                    for region in ctxt.bc().loans_live_at(location) {
                        writeln!(bc_facts_file, "  Region: {region:?}").unwrap();
                    }
                }

                let start_location = RichLocation::Start(location);
                let mid_location = RichLocation::Mid(location);
                write_bc_facts(bc, start_location, &mut bc_facts_file, ctxt);
                write_bc_facts(bc, mid_location, &mut bc_facts_file, ctxt);
            }
        }
        let dot_graph = subset_anywhere(ctxt);
        let file_path = dir_path.join("bc_facts_graph_anywhere.dot");
        dot_graph.write_to_file(&file_path).unwrap();
    }

    let region_inference_dot_graph = region_inference_outlives(ctxt);
    let file_path = dir_path.join("region_inference_outlives.dot");
    std::fs::write(file_path, region_inference_dot_graph).unwrap();
}
