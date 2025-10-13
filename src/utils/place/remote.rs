use crate::{
    borrow_pcg::region_projection::{
        HasRegions, HasTy, PcgLifetimeProjectionBase, PcgLifetimeProjectionBaseLike, PcgRegion,
        PlaceOrConst, RegionIdx,
    },
    pcg::{PcgNode, PcgNodeLike},
    rustc_interface::{
        index::IndexVec,
        middle::{mir, ty},
    },
    utils::{
        self, CompilerCtxt, HasCompilerCtxt, display::DisplayWithCtxt, json::ToJsonWithCtxt,
        validity::HasValidityCheck,
    },
};

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash, PartialOrd, Ord)]
pub struct RemotePlace {
    pub(crate) local: mir::Local,
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
    fn to_json(&self, _repacker: Ctxt) -> serde_json::Value {
        todo!()
    }
}

impl<Ctxt> DisplayWithCtxt<Ctxt> for RemotePlace {
    fn to_short_string(&self, _repacker: Ctxt) -> String {
        format!("Remote({:?})", self.local)
    }
}

impl<'tcx> PcgNodeLike<'tcx> for RemotePlace {
    fn to_pcg_node<C: Copy>(self, _repacker: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx> {
        self.into()
    }
}

impl<'tcx> PcgLifetimeProjectionBaseLike<'tcx> for RemotePlace {
    fn to_pcg_lifetime_projection_base(&self) -> PcgLifetimeProjectionBase<'tcx> {
        PlaceOrConst::Place((*self).into())
    }
}

impl<'tcx> HasValidityCheck<'_, 'tcx> for RemotePlace {
    fn check_validity(&self, _ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        Ok(())
    }
}

impl std::fmt::Display for RemotePlace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Remote({:?})", self.local)
    }
}
