use crate::rustc_interface::middle::mir::HasLocalDecls;

use crate::{
    pcg_validity_assert, pcg_validity_expect_ok, rustc_interface::middle::mir,
    utils::HasCompilerCtxt,
};

use super::CompilerCtxt;

pub trait HasValidityCheck<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx> = CompilerCtxt<'a, 'tcx>> {
    fn check_validity(&self, repacker: Ctxt) -> Result<(), String>;

    fn assert_validity(&self, ctxt: impl Into<Ctxt>) {
        pcg_validity_expect_ok!(self.check_validity(ctxt.into()), fallback: (), [ctxt], "Validity check failed");
    }

    fn assert_validity_at_location(&self, location: mir::Location, ctxt: impl Into<Ctxt>) {
        pcg_validity_expect_ok!(self.check_validity(ctxt.into()), fallback: (), [ctxt at location]);
    }

    fn is_valid(&self, ctxt: impl Into<Ctxt>) -> bool {
        self.check_validity(ctxt.into()).is_ok()
    }
}

impl<'tcx> HasValidityCheck<'_, 'tcx> for mir::Local {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
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
