use crate::{
    borrow_pcg::{
        region_projection::{
            HasRegions, HasTy, LifetimeProjection, PcgLifetimeProjectionBase,
            PcgLifetimeProjectionBaseLike, PcgRegion, PlaceOrConst, RegionIdx,
        },
        visitor::extract_regions,
    },
    pcg::PcgNode,
    rustc_interface::{
        index::IndexVec,
        middle::{mir, ty},
    },
    utils::{
        self, CompilerCtxt, HasCompilerCtxt, HasLocals, LocalTys, Place,
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

impl<'tcx> From<LifetimeProjection<'tcx, RemotePlace>> for PcgNode<'tcx> {
    fn from(projection: LifetimeProjection<'tcx, RemotePlace>) -> Self {
        PcgNode::LifetimeProjection(projection.rebase())
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> HasTy<'tcx, Ctxt> for RemotePlace {
    fn rust_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx> {
        let place: utils::Place<'tcx> = self.local.into();
        place.rust_ty(ctxt)
    }
}

impl<'tcx, Ctxt: LocalTys<'tcx> + Copy> HasRegions<'tcx, Ctxt> for RemotePlace {
    fn regions(&self, ctxt: Ctxt) -> IndexVec<RegionIdx, PcgRegion> {
        extract_regions(ctxt.local_ty(self.local))
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

impl<'tcx, P> PcgLifetimeProjectionBaseLike<'tcx, MaybeRemotePlace<'tcx, P>> for RemotePlace {
    fn to_pcg_lifetime_projection_base(
        &self,
    ) -> PcgLifetimeProjectionBase<'tcx, MaybeRemotePlace<'tcx, P>> {
        PlaceOrConst::Place((*self).into())
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
