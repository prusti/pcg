use crate::{
    borrow_pcg::region_projection::{
        HasRegions, HasTy, LifetimeProjection, PcgLifetimeProjectionBase,
        PcgLifetimeProjectionBaseLike, PcgRegion, PlaceOrConst, RegionIdx,
    },
    pcg::PcgNode,
    rustc_interface::{
        index::IndexVec,
        middle::{mir, ty},
    },
    utils::{
        self, CompilerCtxt, HasCompilerCtxt, Place,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        json::ToJsonWithCtxt,
        validity::HasValidityCheck,
    },
};

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash, PartialOrd, Ord)]
pub struct RemotePlace {
    pub(crate) local: mir::Local,
}

impl RemotePlace {
    pub fn base_lifetime_projection<'a, 'tcx: 'a>(
        self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Option<LifetimeProjection<'tcx, Self>> {
        let local_place: Place<'tcx> = self.local.into();
        let region = local_place.ty_region(ctxt)?;
        Some(LifetimeProjection::new(self, region, None, ctxt).unwrap())
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

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> HasRegions<'tcx, Ctxt> for RemotePlace {
    fn regions(&self, ctxt: Ctxt) -> IndexVec<RegionIdx, PcgRegion> {
        let place: utils::Place<'tcx> = self.local.into();
        place.regions(ctxt)
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

impl<'tcx> PcgLifetimeProjectionBaseLike<'tcx> for RemotePlace {
    fn to_pcg_lifetime_projection_base(&self) -> PcgLifetimeProjectionBase<'tcx> {
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
