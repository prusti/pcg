use derive_more::From;

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
