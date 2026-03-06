use std::cmp::Ordering;

use serde_derive::Serialize;

use crate::{
    pcg::CapabilityKind,
    utils::display::{DisplayOutput, DisplayWithCtxt, OutputMode},
};

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Serialize)]
#[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
pub enum OwnedCapability {
    Deep,
    Uninitialized,
    Shallow,
}

impl<Ctxt: Copy> DisplayWithCtxt<Ctxt> for OwnedCapability {
    fn display_output(&self, _ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        if mode.is_test() || mode.is_short() {
        match self {
            OwnedCapability::Deep => "D".into(),
            OwnedCapability::Uninitialized => "U".into(),
            OwnedCapability::Shallow => "S".into()
        }
        } else {
            format!("{self:?}").into()
        }
    }
}

impl OwnedCapability {
    pub(crate) fn uninitialized(self) -> bool {
        matches!(self, OwnedCapability::Uninitialized)
    }
    pub(crate) fn is_deep(self) -> bool {
        matches!(self, OwnedCapability::Deep)
    }
}

impl<N: PartialEq> PartialEq<CapabilityKind<N>> for OwnedCapability {
    fn eq(&self, other: &CapabilityKind<N>) -> bool {
        let as_capability_kind: CapabilityKind<N> = (*self).into();
        as_capability_kind.eq(other)
    }
}

impl<N: Eq + Copy> PartialOrd<CapabilityKind<N>> for OwnedCapability {
    fn partial_cmp(&self, other: &CapabilityKind<N>) -> Option<Ordering> {
        let as_capability_kind: CapabilityKind<N> = (*self).into();
        as_capability_kind.partial_cmp(other)
    }
}

impl Ord for OwnedCapability {
    fn cmp(&self, other: &Self) -> Ordering {
        if self == other {
            return Ordering::Equal;
        }
        match (self, other) {
            (OwnedCapability::Shallow, OwnedCapability::Deep)
            | (OwnedCapability::Uninitialized, _) => Ordering::Less,
            (OwnedCapability::Deep | OwnedCapability::Shallow, _) => {
                Ordering::Greater
            }
        }
    }
}

impl PartialOrd for OwnedCapability {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
