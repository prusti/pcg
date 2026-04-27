use crate::{
    borrow_pcg::region_projection::{
        HasTy, LifetimeProjection, PcgLifetimeProjectionBase, PcgLifetimeProjectionBaseLike,
        PlaceOrConst,
    },
    pcg::PcgNode,
    rustc_interface::middle::ty,
    utils::{
        CompilerCtxt, HasCompilerCtxt, LocalTys, Place,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        json::ToJsonWithCtxt,
        maybe_remote::MaybeRemotePlace,
        validity::HasValidityCheck,
    },
};

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash, PartialOrd, Ord)]
pub struct DerefRemotePlace<'tcx> {
    pub(crate) place: Place<'tcx>,
}

impl crate::Sealed for DerefRemotePlace<'_> {}

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

impl<'a, 'tcx: 'a, Ctxt: LocalTys<'tcx> + HasCompilerCtxt<'a, 'tcx>> HasTy<'tcx, Ctxt>
    for DerefRemotePlace<'tcx>
{
    fn rust_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx> {
        self.place.ty(ctxt).ty
    }
}

impl<'a, 'tcx, Ctxt: HasCompilerCtxt<'a, 'tcx>> ToJsonWithCtxt<Ctxt> for DerefRemotePlace<'tcx> {
    fn to_json(&self, _ctxt: Ctxt) -> serde_json::Value {
        todo!()
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for DerefRemotePlace<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(format!("Remote({:?})", self.place.display_string(ctxt)).into())
    }
}

impl<'tcx> HasValidityCheck<CompilerCtxt<'_, 'tcx>> for DerefRemotePlace<'tcx> {
    fn check_validity(&self, _ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        Ok(())
    }
}

impl std::fmt::Display for DerefRemotePlace<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Remote({:?})", self.place)
    }
}
