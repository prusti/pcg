use borrowck_body_storage::take_stored_body;
use pcg::{PcgCtxtCreator, run_pcg};
use pcg::rustc_interface::{
    hir::def::DefKind,
    middle::ty::TyCtxt,
    span::def_id::LocalDefId,
};

fn hir_body_owners(tcx: TyCtxt<'_>) -> impl std::iter::Iterator<Item = LocalDefId> + '_ {
    tcx.hir_body_owners()
}

/// # Safety
/// 1. Should be called for the same `tcx` where the borrow-checking occurred.
/// 2. The `config` for the compiler run should have had `override_queries` set to [`set_mir_borrowck`].
pub unsafe fn run_pcg_on_all_fns(tcx: TyCtxt<'_>) {
    let ctxt_creator = PcgCtxtCreator::new(tcx);
    tracing::info!("Running PCG on all functions");

    for def_id in hir_body_owners(tcx) {
        let kind = tcx.def_kind(def_id);
        if !matches!(kind, DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        let item_name = tcx.def_path_str(def_id.to_def_id()).to_string();

        let body = unsafe { take_stored_body(tcx, def_id) };

        tracing::info!(
            "Running PCG on function: {} with {} basic blocks",
            item_name,
            body.body.basic_blocks.len()
        );

        let pcg_ctxt = ctxt_creator.new_nll_ctxt(&body);
        let _ = run_pcg(pcg_ctxt);
    }

    #[cfg(feature = "visualization")]
    ctxt_creator.write_debug_visualization_metadata();
}

