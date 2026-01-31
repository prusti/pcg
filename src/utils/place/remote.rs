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

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash, PartialOrd, Ord)]
pub struct RemotePlace {
    pub(crate) local: mir::Local,
}

impl<'tcx> crate::Sealed for RemotePlace {}

impl RemotePlace {
    pub fn base_lifetime_projection<'tcx>(
        self,
        ctxt: impl LocalTys<'tcx> + Copy,
    ) -> Option<LifetimeProjection<'tcx, Self>> {
        let ty = ctxt.local_ty(self.local);
        match ty.kind() {
            ty::TyKind::Ref(region, _, _) => {
                LifetimeProjection::new(self, (*region).into(), None, ctxt)
            }
            _ => None,
        }
    }
}

impl<'tcx, P> PcgLifetimeProjectionBaseLike<'tcx, P> for RemotePlace {
    fn to_pcg_lifetime_projection_base(&self) -> PcgLifetimeProjectionBase<'tcx, P> {
        PlaceOrConst::Place(MaybeRemotePlace::Remote(*self))
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, RemotePlace>> for PcgNode<'tcx> {
    fn from(projection: LifetimeProjection<'tcx, RemotePlace>) -> Self {
        PcgNode::LifetimeProjection(projection.rebase())
    }
}

impl<'tcx, Ctxt: LocalTys<'tcx>> HasTy<'tcx, Ctxt> for RemotePlace {
    fn rust_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx> {
        ctxt.local_ty(self.local)
    }
}

impl<'a, 'tcx, Ctxt: HasCompilerCtxt<'a, 'tcx>> ToJsonWithCtxt<Ctxt> for RemotePlace {
    fn to_json(&self, _ctxt: Ctxt) -> serde_json::Value {
        todo!()
    }
}

impl<Ctxt> DisplayWithCtxt<Ctxt> for RemotePlace {
    fn display_output(&self, _ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(format!("Remote({:?})", self.local).into())
    }
}

impl<'a, 'tcx> HasValidityCheck<CompilerCtxt<'a, 'tcx>> for RemotePlace {
    fn check_validity(&self, _ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        Ok(())
    }
}

impl std::fmt::Display for RemotePlace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Remote({:?})", self.local)
    }
}
