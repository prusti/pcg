use crate::{
    borrow_checker::BorrowCheckerInterface,
    utils::{CompilerCtxt, CtxtExtra, HasCompilerCtxt},
};

pub trait ToJsonWithCompilerCtxt<'a, 'tcx, BC = ()> {
    fn to_json(&self, repacker: impl HasCompilerCtxt<'a, 'tcx, BC>) -> serde_json::Value;
}

impl<'a, 'tcx, BC: crate::utils::CtxtExtra, T: ToJsonWithCompilerCtxt<'a, 'tcx, BC>>
    ToJsonWithCompilerCtxt<'a, 'tcx, BC> for Vec<T>
{
    fn to_json(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx, BC>) -> serde_json::Value {
        self.iter()
            .map(|a| a.to_json(ctxt))
            .collect::<Vec<_>>()
            .into()
    }
}
