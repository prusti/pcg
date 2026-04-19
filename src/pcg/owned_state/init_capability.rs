use std::{
    cmp::Ordering,
    fmt::{Debug, Formatter},
};

use serde_derive::Serialize;

use crate::{
    pcg::CapabilityKind,
    utils::display::{DisplayOutput, DisplayWithCtxt, OutputMode},
};

/// An *initialisation capability* attached to a leaf of the
/// [`super::InitialisationTree`].
///
/// See <https://prusti.github.io/pcg-docs/owned-state.html#initialisation-capabilities>
/// for the authoritative definition. The total order is
/// `Deep > Shallow > Uninit`.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Serialize)]
pub(crate) enum OwnedCapability {
    /// `D`: fully initialised. All memory reachable from this place
    /// (including through dereferences) is valid and accessible.
    Deep,
    /// `S`: shallowly initialised. The place itself holds a valid value,
    /// but memory behind a dereference may not be. Arises only for
    /// `Box`-typed places where the heap allocation exists but nothing has
    /// been written through it yet.
    Shallow,
    /// `U`: uninitialised or moved out of. Only writes (to re-initialise)
    /// are permitted.
    Uninit,
}

impl OwnedCapability {
    #[must_use]
    pub(crate) fn is_uninit(self) -> bool {
        matches!(self, OwnedCapability::Uninit)
    }

    #[must_use]
    pub(crate) fn is_deep(self) -> bool {
        matches!(self, OwnedCapability::Deep)
    }

    #[must_use]
    pub(crate) fn is_shallow(self) -> bool {
        matches!(self, OwnedCapability::Shallow)
    }

    /// Mapping from an initialisation capability to a `CapabilityKind`,
    /// mirroring the fully-initialised case of
    /// <https://prusti.github.io/pcg-docs/computing-place-capabilities.html>.
    /// A `Deep` leaf with no blocking borrow maps to `Exclusive`; the
    /// other cases map to the capabilities dictated by the
    /// initialisation state alone.
    #[must_use]
    pub(crate) fn as_capability_kind(self) -> CapabilityKind {
        match self {
            OwnedCapability::Deep => CapabilityKind::Exclusive,
            OwnedCapability::Shallow => CapabilityKind::ShallowExclusive,
            OwnedCapability::Uninit => CapabilityKind::Write,
        }
    }
}

impl Debug for OwnedCapability {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            OwnedCapability::Deep => write!(f, "D"),
            OwnedCapability::Shallow => write!(f, "S"),
            OwnedCapability::Uninit => write!(f, "U"),
        }
    }
}

impl Ord for OwnedCapability {
    fn cmp(&self, other: &Self) -> Ordering {
        fn rank(cap: OwnedCapability) -> u8 {
            match cap {
                OwnedCapability::Uninit => 0,
                OwnedCapability::Shallow => 1,
                OwnedCapability::Deep => 2,
            }
        }
        rank(*self).cmp(&rank(*other))
    }
}

impl PartialOrd for OwnedCapability {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<Ctxt: Copy> DisplayWithCtxt<Ctxt> for OwnedCapability {
    fn display_output(&self, _ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        match mode {
            OutputMode::Normal => match self {
                OwnedCapability::Deep => "Deep",
                OwnedCapability::Shallow => "Shallow",
                OwnedCapability::Uninit => "Uninit",
            }
            .into(),
            OutputMode::Short | OutputMode::Test => match self {
                OwnedCapability::Deep => "D",
                OwnedCapability::Shallow => "S",
                OwnedCapability::Uninit => "U",
            }
            .into(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ordering_is_deep_gt_shallow_gt_uninit() {
        assert!(OwnedCapability::Deep > OwnedCapability::Shallow);
        assert!(OwnedCapability::Shallow > OwnedCapability::Uninit);
        assert!(OwnedCapability::Deep > OwnedCapability::Uninit);
    }

    #[test]
    fn as_capability_kind_matches_docs() {
        assert_eq!(
            OwnedCapability::Deep.as_capability_kind(),
            CapabilityKind::Exclusive,
        );
        assert_eq!(
            OwnedCapability::Shallow.as_capability_kind(),
            CapabilityKind::ShallowExclusive,
        );
        assert_eq!(
            OwnedCapability::Uninit.as_capability_kind(),
            CapabilityKind::Write,
        );
    }
}
