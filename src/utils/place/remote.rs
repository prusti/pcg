use crate::borrow_pcg::region_projection::{
    HasTy, PcgLifetimeProjectionBase, PcgLifetimeProjectionBaseLike, PcgRegion, RegionIdx,
};
use crate::borrow_pcg::visitor::extract_regions;
use crate::pcg::{PCGNodeLike, PcgNode};
use crate::rustc_interface::middle::mir;
use crate::rustc_interface::middle::ty;
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::json::ToJsonWithCompilerCtxt;
use crate::utils::validity::HasValidityCheck;
use crate::utils::{self, CompilerCtxt, HasCompilerCtxt, Place};

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash, PartialOrd, Ord)]
pub struct RemotePlace {
    pub(crate) local: mir::Local,
}

impl<'tcx> HasTy<'tcx> for RemotePlace {
    fn rust_ty<'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> ty::Ty<'tcx>
    where
        'tcx: 'a,
    {
        let place: utils::Place<'tcx> = self.local.into();
        place.rust_ty(ctxt)
    }
}

impl<'tcx, BC: Copy> ToJsonWithCompilerCtxt<'tcx, BC> for RemotePlace {
    fn to_json(&self, _repacker: CompilerCtxt<'_, 'tcx, BC>) -> serde_json::Value {
        todo!()
    }
}

impl<'tcx, BC: Copy> DisplayWithCompilerCtxt<'tcx, BC> for RemotePlace {
    fn to_short_string(&self, _repacker: CompilerCtxt<'_, 'tcx, BC>) -> String {
        format!("Remote({:?})", self.local)
    }
}

impl<'tcx> PCGNodeLike<'tcx> for RemotePlace {
    fn to_pcg_node<C: Copy>(self, _repacker: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx> {
        self.into()
    }
}

impl<'tcx> PcgLifetimeProjectionBaseLike<'tcx> for RemotePlace {
    fn to_pcg_lifetime_projection_base(&self) -> PcgLifetimeProjectionBase<'tcx> {
        PcgLifetimeProjectionBase::Place((*self).into())
    }
}

impl<'tcx> HasValidityCheck<'tcx> for RemotePlace {
    fn check_validity(&self, _ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        Ok(())
    }
}

impl std::fmt::Display for RemotePlace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Remote({:?})", self.local)
    }
}
