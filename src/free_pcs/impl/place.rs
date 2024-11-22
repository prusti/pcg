// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    cmp::Ordering,
    fmt::{Debug, Formatter, Result},
};

use rustc_interface::{
    hir::Mutability,
    data_structures::fx::FxHashSet
};

use crate::{rustc_interface, utils::{Place, PlaceOrdering}};

#[derive(Debug)]
pub(crate) struct RelatedSet<'tcx> {
    pub(crate) from: Vec<(Place<'tcx>, CapabilityKind)>,
    pub(crate) to: Place<'tcx>,
    // pub(crate) minimum: CapabilityKind,
    pub(crate) relation: PlaceOrdering,
}
impl<'tcx> RelatedSet<'tcx> {
    pub fn get_from(&self) -> FxHashSet<Place<'tcx>> {
        assert!(matches!(
            self.relation,
            PlaceOrdering::Suffix | PlaceOrdering::Both
        ));
        self.from.iter().map(|(p, _)| *p).collect()
    }
    pub fn get_only_from(&self) -> Place<'tcx> {
        assert_eq!(self.from.len(), 1);
        self.from[0].0
    }
    pub fn common_prefix(&self, to: Place<'tcx>) -> Place<'tcx> {
        self.from[0].0.common_prefix(to)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum CapabilityKind {
    /// For owned places, this capability means that there are outstanding shared
    /// borrows. Their capability will be restored to [`CapabilityKind::Exclusive`]
    /// when their borrows expire.
    ///
    /// Nodes in the borrow PCG transitively originating from a shared
    /// borrow also have this capability.
    Read,

    /// For owned places, this capability is used when the place is moved out
    /// of. This capability is used for both owned and borrowed places just before
    /// they are overwritten.
    Write,

    /// Writes and reads are permitted to this place, and the place is not
    /// borrowed. We use this capability for owned places even if they are
    /// created via immutable bindings.
    Exclusive,

    /// This place is mutably borrowed.
    Lent,

    /// [`CapabilityKind::Exclusive`] for everything not through a dereference,
    /// [`CapabilityKind::Write`] for everything through a dereference.
    ShallowExclusive,
}
impl Debug for CapabilityKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            CapabilityKind::Read => write!(f, "R"),
            CapabilityKind::Write => write!(f, "W"),
            CapabilityKind::Exclusive => write!(f, "E"),
            CapabilityKind::ShallowExclusive => write!(f, "e"),
            CapabilityKind::Lent => write!(f, "L"),
        }
    }
}

impl PartialOrd for CapabilityKind {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if *self == *other {
            return Some(Ordering::Equal);
        }
        match (self, other) {
            // W < E, W < e
            (CapabilityKind::Lent, _)
            | (_, CapabilityKind::Exclusive)
            | (CapabilityKind::Write, CapabilityKind::ShallowExclusive) => Some(Ordering::Less),
            // E > W, e > W
            (CapabilityKind::Exclusive, _)
            | (_, CapabilityKind::Lent)
            | (CapabilityKind::ShallowExclusive, CapabilityKind::Write) => Some(Ordering::Greater),
            _ => None,
        }
    }
}

impl CapabilityKind {
    pub fn is_exclusive(self) -> bool {
        matches!(self, CapabilityKind::Exclusive)
    }
    pub fn is_lent_exclusive(self) -> bool {
        matches!(self, CapabilityKind::Lent)
    }
    pub fn is_read(self) -> bool {
        matches!(self, CapabilityKind::Read)
    }
    pub fn is_write(self) -> bool {
        matches!(self, CapabilityKind::Write)
    }
    pub fn is_shallow_exclusive(self) -> bool {
        matches!(self, CapabilityKind::ShallowExclusive)
    }
    pub fn minimum(self, other: Self) -> Option<Self> {
        match self.partial_cmp(&other)? {
            Ordering::Greater => Some(other),
            _ => Some(self),
        }
    }
}
