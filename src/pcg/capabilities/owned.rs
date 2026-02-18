use std::cmp::Ordering;

use crate::pcg::{CapabilityKind, CapabilityLike};

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
#[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
pub(crate) enum OwnedCapability {
    Exclusive,
    Write,
    ShallowExclusive,
}

impl Ord for OwnedCapability {
    fn cmp(&self, other: &Self) -> Ordering {
        if self == other {
            return Ordering::Equal;
        }
        match (self, other) {
            (OwnedCapability::Exclusive, _) => Ordering::Greater,
            (OwnedCapability::ShallowExclusive, OwnedCapability::Exclusive) => Ordering::Less,
            (OwnedCapability::ShallowExclusive, _) => Ordering::Greater,
            (OwnedCapability::Write, _) => Ordering::Less,
        }
    }
}

impl PartialOrd for OwnedCapability {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
