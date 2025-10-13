use crate::utils::CompilerCtxt;

pub trait ToJsonWithCtxt<Ctxt> {
    fn to_json(&self, ctxt: Ctxt) -> serde_json::Value;
}

pub trait ToJsonWithCompilerCtxt<'a, 'tcx: 'a, BC> = ToJsonWithCtxt<CompilerCtxt<'a, 'tcx, BC>>;

impl<Ctxt: Copy, T: ToJsonWithCtxt<Ctxt>> ToJsonWithCtxt<Ctxt> for Vec<T> {
    fn to_json(&self, ctxt: Ctxt) -> serde_json::Value {
        self.iter()
            .map(|a| a.to_json(ctxt))
            .collect::<Vec<_>>()
            .into()
    }
}
