use crate::rustc_interface::middle::mir::HasLocalDecls;

use crate::utils::{DebugCtxt, HasCompilerCtxt};
use crate::{pcg_validity_assert, pcg_validity_expect_ok, rustc_interface::middle::mir};

use super::CompilerCtxt;

pub trait HasValidityCheck<Ctxt: DebugCtxt + Copy> {
    fn check_validity(&self, ctxt: Ctxt) -> Result<(), String>;

    fn assert_validity(&self, ctxt: Ctxt) {
        pcg_validity_expect_ok!(self.check_validity(ctxt), fallback: (), [ctxt], "Validity check failed");
    }

    fn assert_validity_at_location(&self, location: mir::Location, ctxt: Ctxt) {
        pcg_validity_expect_ok!(self.check_validity(ctxt), fallback: (), [ctxt at location]);
    }

    fn is_valid(&self, ctxt: Ctxt) -> bool {
        self.check_validity(ctxt).is_ok()
    }
}

macro_rules! has_validity_check_node_wrapper {
    ($ty:ty) => {
        impl<'tcx, Ctxt: DebugCtxt + Copy, P> HasValidityCheck<Ctxt> for $ty
        where
            <Self as std::ops::Deref>::Target: HasValidityCheck<Ctxt>,
        {
            fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
                use std::ops::Deref;
                self.deref().check_validity(ctxt)
            }
        }
    };
}
pub(crate) use has_validity_check_node_wrapper;

impl<'a, 'tcx: 'a, Ctxt: DebugCtxt + HasCompilerCtxt<'a, 'tcx>> HasValidityCheck<Ctxt>
    for mir::Local
{
    fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
        if ctxt.body().local_decls().len() <= self.as_usize() {
            return Err(format!(
                "Local {:?} is out of bounds: provided MIR at {:?} only has {} local declarations",
                self,
                ctxt.body().span,
                ctxt.body().local_decls().len()
            ));
        }
        Ok(())
    }
}
