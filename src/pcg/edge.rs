use serde_derive::Serialize;

use crate::utils::display::{DisplayOutput, DisplayWithCtxt, OutputMode};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
pub enum EdgeMutability {
    Mutable,
    Immutable,
}

impl <Ctxt> DisplayWithCtxt<Ctxt> for EdgeMutability {
    fn display_output(&self, _ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        if mode.is_test() {
            return DisplayOutput::Text(match self {
                EdgeMutability::Mutable => "E".into(),
                EdgeMutability::Immutable => "R".into(),
            });
        }
        format!("{self:?}").into()
    }
}
