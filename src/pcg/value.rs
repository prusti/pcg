//! How the parts of a place relate to it. Each projection step has a kind,
//! which decides what a capability held by the base gives the part, what the
//! base keeps, whether the part is stored in the base, and whether loans of
//! the part are tracked. The value, storage and loan conflicts of a place
//! (see [`crate::utils::PlaceLike`]) are read off these steps.
//!
//! The rules follow rustc's borrow checker: a loan through a shared reference
//! or a raw pointer is never tracked (`ignore_borrow`); a deep access (read,
//! move, borrow) conflicts with loans past fields, Box contents and mutable
//! references; an assignment conflicts with no loan past any dereference, and
//! the drop of the old value with loans in Box contents.

use crate::pcg::CapabilityKind;

/// How a projection step relates a part to its base.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StepKind {
    /// A field, an enum variant, an array element or a cast: the part is
    /// stored in the base.
    Owned,
    /// The contents of a Box, which the Box owns.
    BoxDeref,
    /// The referent of a mutable reference. A loan of it keeps the reference
    /// from being read or moved, but not from being overwritten.
    MutDeref,
    /// The referent of a shared reference, which is only read through it.
    SharedDeref,
    /// The referent of a raw pointer. It gets nothing from the pointer's
    /// capability: unpacking the pointer for an unsafe access gives it the
    /// capability that access needs.
    RawDeref,
}

impl StepKind {
    /// Whether overwriting or dropping the base replaces the part.
    pub(crate) fn is_storage(self) -> bool {
        matches!(self, StepKind::Owned | StepKind::BoxDeref)
    }

    /// Whether loans of places past this step are tracked. rustc ignores
    /// loans through a shared reference or a raw pointer: the path to them is
    /// `Copy`, so nothing done to it can invalidate the loan.
    pub(crate) fn tracks_loans(self) -> bool {
        !matches!(self, StepKind::SharedDeref | StepKind::RawDeref)
    }

    /// The capability the part gets when its base, holding `capability`, is
    /// unpacked across this step.
    pub(crate) fn share(self, capability: CapabilityKind) -> Option<CapabilityKind> {
        match (self, capability) {
            (StepKind::Owned, capability) => Some(capability),
            (StepKind::BoxDeref | StepKind::MutDeref, CapabilityKind::Exclusive) => {
                Some(CapabilityKind::Exclusive)
            }
            (
                StepKind::BoxDeref | StepKind::MutDeref | StepKind::SharedDeref,
                CapabilityKind::Read,
            )
            | (StepKind::SharedDeref, CapabilityKind::Exclusive) => Some(CapabilityKind::Read),
            _ => None,
        }
    }

    /// The capability the base keeps when it is unpacked across this step,
    /// holding `capability`: a stored part takes it over, a mutable reference
    /// keeps e of E, a dereferenced shared reference is read, and a raw
    /// pointer keeps what it holds.
    pub(crate) fn kept(self, capability: CapabilityKind) -> Option<CapabilityKind> {
        match (self, capability) {
            (StepKind::Owned | StepKind::BoxDeref, _) => None,
            (StepKind::MutDeref, CapabilityKind::Exclusive) => {
                Some(CapabilityKind::ShallowExclusive)
            }
            (StepKind::SharedDeref, CapabilityKind::Exclusive) => Some(CapabilityKind::Read),
            (_, capability) => Some(capability),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::StepKind;
    use crate::pcg::CapabilityKind::{
        Exclusive as E, Read as R, ShallowExclusive as Se, Write as W,
    };

    #[test]
    fn shares() {
        assert_eq!(StepKind::Owned.share(W), Some(W));
        assert_eq!(StepKind::BoxDeref.share(E), Some(E));
        assert_eq!(StepKind::BoxDeref.share(W), None);
        assert_eq!(StepKind::MutDeref.share(E), Some(E));
        assert_eq!(StepKind::MutDeref.share(R), Some(R));
        assert_eq!(StepKind::MutDeref.share(Se), None);
        assert_eq!(StepKind::SharedDeref.share(E), Some(R));
        assert_eq!(StepKind::RawDeref.share(E), None);
    }

    #[test]
    fn kept() {
        assert_eq!(StepKind::Owned.kept(E), None);
        assert_eq!(StepKind::MutDeref.kept(E), Some(Se));
        assert_eq!(StepKind::MutDeref.kept(R), Some(R));
        assert_eq!(StepKind::SharedDeref.kept(E), Some(R));
        assert_eq!(StepKind::RawDeref.kept(E), Some(E));
    }
}
