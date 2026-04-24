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
pub struct DerefRemotePlace {
    pub(crate) cnt_derefs: usize,
    pub(crate) local: mir::Local,
}

impl crate::Sealed for DerefRemotePlace {}

impl<'tcx, P> PcgLifetimeProjectionBaseLike<'tcx, P> for DerefRemotePlace {
    fn to_pcg_lifetime_projection_base(&self) -> PcgLifetimeProjectionBase<'tcx, P> {
        PlaceOrConst::Place(MaybeRemotePlace::DerefRemote(*self))
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, DerefRemotePlace>> for PcgNode<'tcx> {
    fn from(projection: LifetimeProjection<'tcx, DerefRemotePlace>) -> Self {
        PcgNode::LifetimeProjection(projection.rebase())
    }
}

impl<'tcx, Ctxt: LocalTys<'tcx>> HasTy<'tcx, Ctxt> for DerefRemotePlace {
    fn rust_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx> {
        let mut ty = ctxt.local_ty(self.local);
        for _i in 0..self.cnt_derefs {
            ty = ty.builtin_deref(true).expect("Number of derefs does not match for DerefRemotePlace");
        }
        ty
    }
}

impl<'a, 'tcx, Ctxt: HasCompilerCtxt<'a, 'tcx>> ToJsonWithCtxt<Ctxt> for DerefRemotePlace {
    fn to_json(&self, _ctxt: Ctxt) -> serde_json::Value {
        todo!()
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt> for DerefRemotePlace {
    fn display_output(&self, ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(format!("{:*<1$}Remote({2:?})", "", self.cnt_derefs, self.local.display_string(ctxt)).into())
    }
}

impl<'tcx> HasValidityCheck<CompilerCtxt<'_, 'tcx>> for DerefRemotePlace {
    fn check_validity(&self, _ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        Ok(())
    }
}

impl std::fmt::Display for DerefRemotePlace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:*<1$}Remote({2:?})", "", self.cnt_derefs, self.local)
    }
}
