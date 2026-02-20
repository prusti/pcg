use serde_derive::Serialize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
pub enum EdgeMutability {
    Mutable,
    Immutable,
}
