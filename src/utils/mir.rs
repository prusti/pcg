use derive_more::{Deref, From};
use pcg_macros::DisplayWithCtxt;

use crate::rustc_interface::middle::mir;

#[derive(Copy, Clone, From, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
pub struct BasicBlock(#[cfg_attr(feature = "type-export", ts(type = "string"))] mir::BasicBlock);

impl std::fmt::Debug for BasicBlock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl serde::Serialize for BasicBlock {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        format!("{:?}", self.0).serialize(serializer)
    }
}

#[derive(From, Deref, Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct Local(mir::Local);

#[cfg(feature = "type-export")]
impl ts_rs::TS for Local {
    type WithoutGenerics = Local;
    type OptionInnerType = Local;

    fn name(cfg: &ts_rs::Config) -> String {
        todo!()
    }

    fn inline(cfg: &ts_rs::Config) -> String {
        todo!()
    }
}
