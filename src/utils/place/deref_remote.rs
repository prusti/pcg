use crate::{
    borrow_pcg::region_projection::{
        HasTy, LifetimeProjection, PcgLifetimeProjectionBase, PcgLifetimeProjectionBaseLike,
        PlaceOrConst,
    },
    pcg::PcgNode,
    rustc_interface::middle::{mir, ty},
    utils::{
        CompilerCtxt, HasCompilerCtxt, LocalTys,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        json::ToJsonWithCtxt,
        maybe_remote::MaybeRemotePlace,
        validity::HasValidityCheck,
    },
};

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash)]
pub struct DerefRemotePlace<'tcx> {
    pub(crate) cnt_derefs: usize,
    pub(crate) local: mir::Local,
    pub(crate) ty: ty::Ty<'tcx>,
}

impl<'tcx> crate::Sealed for DerefRemotePlace<'tcx> {}

impl<'tcx, P> PcgLifetimeProjectionBaseLike<'tcx, P> for DerefRemotePlace<'tcx> {
    fn to_pcg_lifetime_projection_base(&self) -> PcgLifetimeProjectionBase<'tcx, P> {
        PlaceOrConst::Place(MaybeRemotePlace::DerefRemote(*self))
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, DerefRemotePlace<'tcx>>> for PcgNode<'tcx> {
    fn from(projection: LifetimeProjection<'tcx, DerefRemotePlace<'tcx>>) -> Self {
        PcgNode::LifetimeProjection(projection.rebase())
    }
}

impl<'tcx, Ctxt: LocalTys<'tcx>> HasTy<'tcx, Ctxt> for DerefRemotePlace<'tcx> {
    fn rust_ty(&self, _ctxt: Ctxt) -> ty::Ty<'tcx> {
        self.ty
    }
}

impl<'a, 'tcx, Ctxt: HasCompilerCtxt<'a, 'tcx>> ToJsonWithCtxt<Ctxt> for DerefRemotePlace<'tcx> {
    fn to_json(&self, _ctxt: Ctxt) -> serde_json::Value {
        todo!()
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt> for DerefRemotePlace<'tcx> {
    fn display_output(&self, ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(
            format!(
                "{:*<1$}Remote({2:?})",
                "",
                self.cnt_derefs,
                self.local.display_string(ctxt)
            )
            .into(),
        )
    }
}

impl<'tcx> HasValidityCheck<CompilerCtxt<'_, 'tcx>> for DerefRemotePlace<'tcx> {
    fn check_validity(&self, _ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        Ok(())
    }
}

impl<'tcx> std::fmt::Display for DerefRemotePlace<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:*<1$}Remote({2:?})", "", self.cnt_derefs, self.local)
    }
}

impl<'tcx> PartialOrd for DerefRemotePlace<'tcx> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match self.cnt_derefs.partial_cmp(&other.cnt_derefs) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        match self.local.partial_cmp(&other.local) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        Some(core::cmp::Ordering::Equal) // if both places refer to the same place they need to have the same ty
    }
}

impl<'tcx> Ord for DerefRemotePlace<'tcx> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.cnt_derefs.cmp(&other.cnt_derefs) {
            core::cmp::Ordering::Equal => {}
            ord => return ord,
        }
        match self.local.cmp(&other.local) {
            core::cmp::Ordering::Equal => {}
            ord => return ord,
        }
        core::cmp::Ordering::Equal // if both places refer to the same place they need to have the same ty
    }
}