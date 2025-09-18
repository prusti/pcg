use crate::{
    borrow_pcg::region_projection::{
        HasTy, PcgLifetimeProjectionBase, PcgLifetimeProjectionBaseLike, PlaceOrConst,
    },
    pcg::{PcgNode, PcgNodeLike},
    rustc_interface::middle::{mir, ty},
    utils::{
        self, CompilerCtxt, HasCompilerCtxt, display::DisplayWithCompilerCtxt,
        json::ToJsonWithCompilerCtxt, validity::HasValidityCheck,
    },
};

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
