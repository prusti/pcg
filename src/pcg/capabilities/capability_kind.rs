use crate::{
    borrow_pcg::graph::BorrowedCapability,
    pcg::OwnedCapability,
    utils::display::{DisplayOutput, DisplayWithCtxt, OutputMode},
};
use std::{
    cmp::Ordering,
    fmt::{Debug, Formatter, Result},
};

/// Macro for generating patterns that match a capability and all "greater" capabilities
/// according to the partial ordering.
///
/// Usage:
/// ```ignore
/// match cap {
///     capability_gte!(Read) => { /* matches Read or Exclusive */ }
///     capability_gte!(Write) => { /* matches Write, ShallowExclusive, or Exclusive */ }
///     capability_gte!(ShallowExclusive) => { /* matches ShallowExclusive or Exclusive */ }
///     capability_gte!(Exclusive) => { /* matches only Exclusive */ }
/// }
/// ```
///
/// Also supports single-letter abbreviations:
/// ```ignore
/// match cap {
///     capability_gte!(R) => { /* matches Read or Exclusive */ }
///     capability_gte!(W) => { /* matches Write, ShallowExclusive, or Exclusive */ }
///     capability_gte!(e) => { /* matches ShallowExclusive or Exclusive */ }
///     capability_gte!(E) => { /* matches only Exclusive */ }
/// }
/// ```
#[macro_export]
macro_rules! capability_gte {
    // Full names
    (Read) => {
        CapabilityKind::Read | CapabilityKind::Exclusive
    };
    (Write) => {
        CapabilityKind::Write | CapabilityKind::ShallowExclusive | CapabilityKind::Exclusive
    };
    (ShallowExclusive) => {
        CapabilityKind::ShallowExclusive | CapabilityKind::Exclusive
    };
    (Exclusive) => {
        CapabilityKind::Exclusive
    };

    // Single-letter abbreviations
    (R) => {
        CapabilityKind::Read | CapabilityKind::Exclusive
    };
    (W) => {
        CapabilityKind::Write | CapabilityKind::ShallowExclusive | CapabilityKind::Exclusive
    };
    (e) => {
        CapabilityKind::ShallowExclusive | CapabilityKind::Exclusive
    };
    (E) => {
        CapabilityKind::Exclusive
    };
}

pub type PositiveCapability = CapabilityKind<!>;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "type-export", ts(as="debug_reprs::CapabilityDebugRepr", concrete(NoCapability=String)))]
pub enum CapabilityKind<NoCapability = ()> {
    /// For borrowed places only: permits reads from the location, but not writes or
    /// drops.
    Read,

    /// For owned places, this capability is used when the place is moved out
    /// of. This capability is used for both owned and borrowed places just before
    /// they are overwritten.
    Write,

    /// Writes and reads are permitted to this place, and the place is not
    /// borrowed.
    Exclusive,

    /// [`CapabilityKind::Exclusive`] for everything not through a dereference,
    /// [`CapabilityKind::Write`] for everything through a dereference.
    ShallowExclusive,

    None(NoCapability),
}

impl<N> CapabilityKind<N> {
    pub(crate) fn into_owned_capability(self) -> Option<OwnedCapability> {
        match self {
            CapabilityKind::ShallowExclusive => Some(OwnedCapability::ShallowExclusive),
            CapabilityKind::Write => Some(OwnedCapability::Write),
            CapabilityKind::Exclusive => Some(OwnedCapability::Exclusive),
            _ => None,
        }
    }
}

impl<N> From<OwnedCapability> for CapabilityKind<N> {
    fn from(cap: OwnedCapability) -> Self {
        match cap {
            OwnedCapability::Exclusive => CapabilityKind::Exclusive,
            OwnedCapability::Write => CapabilityKind::Write,
            OwnedCapability::ShallowExclusive => CapabilityKind::ShallowExclusive,
        }
    }
}

impl From<BorrowedCapability> for CapabilityKind {
    fn from(value: BorrowedCapability) -> Self {
        match value {
            BorrowedCapability::Exclusive => CapabilityKind::Exclusive,
            BorrowedCapability::Read => CapabilityKind::Read,
            BorrowedCapability::None => CapabilityKind::None(()),
        }
    }
}

impl CapabilityKind {
    pub(crate) fn is_none(self) -> bool {
        matches!(self, CapabilityKind::None(_))
    }
}

pub(crate) mod debug_reprs {
    use serde_derive::Serialize;

    use crate::{
        pcg::{CapabilityKind, PositiveCapability},
        utils::DebugRepr,
    };

    impl<Ctxt> DebugRepr<Ctxt> for CapabilityKind {
        type Repr = CapabilityDebugRepr;
        fn debug_repr(&self, _ctxt: Ctxt) -> Self::Repr {
            match self {
                CapabilityKind::Read => CapabilityDebugRepr::Read,
                CapabilityKind::Write => CapabilityDebugRepr::Write,
                CapabilityKind::Exclusive => CapabilityDebugRepr::Exclusive,
                CapabilityKind::ShallowExclusive => CapabilityDebugRepr::ShallowExclusive,
                CapabilityKind::None(()) => CapabilityDebugRepr::None,
            }
        }
    }

    impl<Ctxt> DebugRepr<Ctxt> for PositiveCapability {
        type Repr = PositiveCapabilityDebugRepr;
        fn debug_repr(&self, _ctxt: Ctxt) -> Self::Repr {
            match *self {
                PositiveCapability::Read => PositiveCapabilityDebugRepr::Read,
                PositiveCapability::Write => PositiveCapabilityDebugRepr::Write,
                PositiveCapability::Exclusive => PositiveCapabilityDebugRepr::Exclusive,
                PositiveCapability::ShallowExclusive => {
                    PositiveCapabilityDebugRepr::ShallowExclusive
                }
                PositiveCapability::None(_) => unreachable!(),
            }
        }
    }

    #[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
    #[derive(Serialize)]
    pub enum CapabilityDebugRepr {
        Read,
        Write,
        Exclusive,
        ShallowExclusive,
        None,
    }

    #[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
    #[derive(Serialize)]
    pub enum PositiveCapabilityDebugRepr {
        Read,
        Write,
        Exclusive,
        ShallowExclusive,
    }
}

impl<N> serde::Serialize for CapabilityKind<N> {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&self.to_short_string(()))
    }
}

impl From<PositiveCapability> for CapabilityKind {
    fn from(cap: PositiveCapability) -> Self {
        cap.into_capability_kind()
    }
}

impl PartialEq<PositiveCapability> for CapabilityKind {
    fn eq(&self, other: &PositiveCapability) -> bool {
        self.into_positive() == Some(*other)
    }
}

impl PartialOrd<PositiveCapability> for CapabilityKind {
    fn partial_cmp(&self, other: &PositiveCapability) -> Option<Ordering> {
        let Some(positive) = self.into_positive() else {
            return Some(Ordering::Less);
        };
        positive.partial_cmp(other)
    }
}

impl<T> Debug for CapabilityKind<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}", self.to_short_string(()))
    }
}

impl<N: Copy + Eq> PartialOrd<CapabilityKind<N>> for CapabilityKind<N> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if *self == *other {
            return Some(Ordering::Equal);
        }

        use CapabilityKind::{Exclusive, Read, ShallowExclusive, Write};
        match (*self, *other) {
            (ShallowExclusive | Read, Exclusive)
            | (Write, ShallowExclusive | Exclusive)
            | (CapabilityKind::None(_), _) => Some(Ordering::Less),
            (Exclusive, _)
            | (ShallowExclusive, Write | CapabilityKind::None(_))
            | (Read, CapabilityKind::None(_)) => Some(Ordering::Greater),
            _ => None,
        }
    }
}

impl<Ctxt, N> DisplayWithCtxt<Ctxt> for CapabilityKind<N> {
    fn display_output(&self, _ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        let str = match mode {
            OutputMode::Normal => match *self {
                CapabilityKind::Read => "Read",
                CapabilityKind::Write => "Write",
                CapabilityKind::Exclusive => "Exclusive",
                CapabilityKind::ShallowExclusive => "ShallowExclusive",
                CapabilityKind::None(_) => "None",
            },
            OutputMode::Short | OutputMode::Test => match *self {
                CapabilityKind::Read => "R",
                CapabilityKind::Write => "W",
                CapabilityKind::Exclusive => "E",
                CapabilityKind::ShallowExclusive => "e",
                CapabilityKind::None(_) => "∅",
            },
        };
        DisplayOutput::Text(str.into())
    }
}

impl<T> CapabilityKind<T> {
    pub(crate) fn into_capability_kind(self) -> CapabilityKind<()> {
        match self {
            CapabilityKind::Read => CapabilityKind::Read,
            CapabilityKind::Write => CapabilityKind::Write,
            CapabilityKind::Exclusive => CapabilityKind::Exclusive,
            CapabilityKind::ShallowExclusive => CapabilityKind::ShallowExclusive,
            CapabilityKind::None(_) => CapabilityKind::None(()),
        }
    }
    pub(crate) fn into_positive(self) -> Option<PositiveCapability> {
        match self {
            CapabilityKind::Read => Some(PositiveCapability::Read),
            CapabilityKind::Write => Some(PositiveCapability::Write),
            CapabilityKind::Exclusive => Some(PositiveCapability::Exclusive),
            CapabilityKind::ShallowExclusive => Some(PositiveCapability::ShallowExclusive),
            CapabilityKind::None(_) => None,
        }
    }
    #[must_use]
    pub fn is_exclusive(self) -> bool {
        matches!(self, CapabilityKind::Exclusive)
    }
    #[must_use]
    pub fn is_read(self) -> bool {
        matches!(self, CapabilityKind::Read)
    }
    #[must_use]
    pub fn is_write(self) -> bool {
        matches!(self, CapabilityKind::Write)
    }
    #[must_use]
    pub fn is_shallow_exclusive(self) -> bool {
        matches!(self, CapabilityKind::ShallowExclusive)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_capability_kind_dag_reachability() {
        use petgraph::{algo::has_path_connecting, graph::DiGraph};

        // Create directed graph
        let mut graph = DiGraph::new();
        let mut node_indices = HashMap::new();

        let caps = [
            PositiveCapability::Exclusive,
            PositiveCapability::ShallowExclusive,
            PositiveCapability::Write,
            PositiveCapability::Read,
        ];
        // Add nodes
        for cap in caps {
            node_indices.insert(cap, graph.add_node(cap));
        }

        // Add edges (a -> b means a is greater than b)
        let edges = [
            (
                PositiveCapability::Exclusive,
                PositiveCapability::ShallowExclusive,
            ),
            (
                PositiveCapability::ShallowExclusive,
                PositiveCapability::Write,
            ),
            (PositiveCapability::Exclusive, PositiveCapability::Read),
        ];

        for (from, to) in edges {
            graph.add_edge(node_indices[&from], node_indices[&to], ());
        }

        // Test that partial_cmp matches graph reachability
        for a in caps {
            for b in caps {
                if a == b {
                    assert!(a.partial_cmp(&b) == Some(Ordering::Equal));
                } else if has_path_connecting(&graph, node_indices[&a], node_indices[&b], None) {
                    assert!(a.partial_cmp(&b) == Some(Ordering::Greater));
                } else if has_path_connecting(&graph, node_indices[&b], node_indices[&a], None) {
                    assert!(a.partial_cmp(&b) == Some(Ordering::Less));
                } else {
                    assert!(a.partial_cmp(&b).is_none());
                }
            }
        }
    }
}
