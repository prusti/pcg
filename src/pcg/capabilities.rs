use crate::{
    pcg_validity_assert,
    rustc_interface::index::{Idx, IndexVec},
    utils::{
        data_structures::HashMap,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
    },
};
use std::{
    cell::RefCell,
    cmp::Ordering,
    fmt::{Debug, Formatter, Result},
};

use derive_more::From;

use crate::{
    pcg::PcgArena,
    utils::{Place, SnapshotLocation, data_structures::HashSet},
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

#[allow(dead_code)]
pub(crate) enum ConstraintResult<'arena> {
    Unsat,
    Sat(Option<CapabilityConstraint<'arena>>),
}

#[allow(dead_code)]
impl ConstraintResult<'_> {
    pub(crate) fn is_sat(&self) -> bool {
        matches!(self, ConstraintResult::Sat(_))
    }
}

#[allow(dead_code)]
pub(crate) struct Choice {
    num_options: usize,
}

impl Choice {
    pub(crate) fn new(num_options: usize) -> Self {
        Self { num_options }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub(crate) struct ChoiceIdx(usize);

impl Idx for ChoiceIdx {
    fn new(index: usize) -> Self {
        Self(index)
    }

    fn index(self) -> usize {
        self.0
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub(crate) struct Decision(usize);

impl Idx for Decision {
    fn new(index: usize) -> Self {
        Self(index)
    }

    fn index(self) -> usize {
        self.0
    }
}

#[allow(dead_code)]
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub(crate) enum CapabilityConstraint<'a> {
    Decision {
        choice: ChoiceIdx,
        decision: Decision,
    },
    Lt(SymbolicCapability, SymbolicCapability),
    #[allow(dead_code)]
    Lte(SymbolicCapability, SymbolicCapability),
    Eq(SymbolicCapability, SymbolicCapability),
    All(&'a [CapabilityConstraint<'a>]),
    Any(&'a [CapabilityConstraint<'a>]),
    Not(&'a CapabilityConstraint<'a>),
    False,
    True,
}

use CapabilityConstraint::{All, False, True};
#[allow(dead_code)]
impl<'a> CapabilityConstraint<'a> {
    pub(crate) fn implies(self, other: Self, arena: PcgArena<'a>) -> Self {
        CapabilityConstraint::not(arena.alloc(self)).or(other, arena)
    }

    pub(crate) fn not(constraint: &'a CapabilityConstraint<'a>) -> Self {
        CapabilityConstraint::Not(constraint)
    }

    pub(crate) fn or(self, other: Self, arena: PcgArena<'a>) -> Self {
        CapabilityConstraint::Any(arena.alloc(vec![self, other]))
    }

    pub(crate) fn all(caps: &'a [CapabilityConstraint<'a>]) -> Self {
        CapabilityConstraint::All(caps)
    }

    pub(crate) fn and(self, other: Self, arena: PcgArena<'a>) -> Self {
        match (self, other) {
            (All(xs), All(ys)) => {
                All(arena.alloc(xs.iter().chain(ys.iter()).copied().collect::<Vec<_>>()))
            }
            _ => todo!(),
        }
    }

    pub(crate) fn all_read(places: &[SymbolicCapability], arena: PcgArena<'a>) -> Self {
        Self::all_eq(
            places,
            SymbolicCapability::Concrete(CapabilityKind::Read),
            arena,
        )
    }

    pub(crate) fn all_exclusive(places: &[SymbolicCapability], arena: PcgArena<'a>) -> Self {
        Self::all_eq(
            places,
            SymbolicCapability::Concrete(CapabilityKind::Exclusive),
            arena,
        )
    }

    pub(crate) fn all_eq(
        places: &[SymbolicCapability],
        cap: SymbolicCapability,
        arena: PcgArena<'a>,
    ) -> Self {
        let mut conds = HashSet::default();
        for place_cap in places.iter().copied() {
            match CapabilityConstraint::eq(place_cap, cap) {
                True => {}
                False => return False,
                result => {
                    conds.insert(result);
                }
            }
        }
        CapabilityConstraint::all(arena.alloc(conds.into_iter().collect::<Vec<_>>()))
    }

    pub(crate) fn lt(
        lhs: impl Into<SymbolicCapability>,
        rhs: impl Into<SymbolicCapability>,
    ) -> Self {
        CapabilityConstraint::Lt(lhs.into(), rhs.into())
    }

    pub(crate) fn eq(
        lhs: impl Into<SymbolicCapability>,
        rhs: impl Into<SymbolicCapability>,
    ) -> Self {
        CapabilityConstraint::Eq(lhs.into(), rhs.into())
    }

    #[allow(dead_code)]
    pub(crate) fn lte(
        lhs: impl Into<SymbolicCapability>,
        rhs: impl Into<SymbolicCapability>,
    ) -> Self {
        CapabilityConstraint::Lte(lhs.into(), rhs.into())
    }

    #[allow(dead_code)]
    pub(crate) fn gte(
        lhs: impl Into<SymbolicCapability>,
        rhs: impl Into<SymbolicCapability>,
    ) -> Self {
        CapabilityConstraint::Lte(rhs.into(), lhs.into())
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct SymbolicCapabilityConstraints<'tcx>(HashSet<CapabilityConstraint<'tcx>>);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, From)]
pub struct CapabilityVar(usize);

pub(crate) struct Choices {
    choices: Vec<Choice>,
}

impl Choices {
    fn new() -> Self {
        Self { choices: vec![] }
    }
    fn add_choice(&mut self, choice: Choice) -> ChoiceIdx {
        self.choices.push(choice);
        ChoiceIdx(self.choices.len() - 1)
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub(crate) struct PlaceAtLocation<'tcx> {
    place: Place<'tcx>,
    location: SnapshotLocation,
}

impl<'tcx> PlaceAtLocation<'tcx> {
    fn new(place: Place<'tcx>, location: SnapshotLocation) -> Self {
        Self { place, location }
    }
}

pub(crate) struct CapabilityVars<'tcx>(Vec<PlaceAtLocation<'tcx>>);

impl<'tcx> CapabilityVars<'tcx> {
    fn contains(&self, pl: PlaceAtLocation<'tcx>) -> bool {
        self.0.contains(&pl)
    }

    fn insert(&mut self, pl: PlaceAtLocation<'tcx>) -> CapabilityVar {
        pcg_validity_assert!(!self.contains(pl));
        self.0.push(pl);
        CapabilityVar(self.0.len() - 1)
    }
}

#[allow(dead_code)]
#[derive(Clone, Copy)]
pub(crate) struct SymbolicCapabilityCtxt<'a, 'tcx> {
    constraints: &'a RefCell<SymbolicCapabilityConstraints<'a>>,
    vars: &'a RefCell<CapabilityVars<'tcx>>,
    choices: &'a RefCell<Choices>,
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum IntroduceConstraints<'tcx> {
    ExpandForSharedBorrow {
        base_place: Place<'tcx>,
        expansion_places: Vec<Place<'tcx>>,
        before_location: SnapshotLocation,
        after_location: SnapshotLocation,
    },
}

#[allow(dead_code)]
impl<'tcx> IntroduceConstraints<'tcx> {
    pub(crate) fn before_location(&self) -> SnapshotLocation {
        match self {
            IntroduceConstraints::ExpandForSharedBorrow {
                before_location, ..
            } => *before_location,
        }
    }

    pub(crate) fn after_location(&self) -> SnapshotLocation {
        match self {
            IntroduceConstraints::ExpandForSharedBorrow { after_location, .. } => *after_location,
        }
    }

    pub(crate) fn affected_places(&self) -> impl Iterator<Item = Place<'tcx>> {
        match self {
            IntroduceConstraints::ExpandForSharedBorrow {
                base_place,
                expansion_places,
                ..
            } => expansion_places
                .iter()
                .chain(std::iter::once(base_place))
                .copied(),
        }
    }
}

pub(crate) struct CapabilityRule<'a, 'tcx> {
    pub(crate) pre: CapabilityConstraint<'a>,
    pub(crate) post: HashMap<Place<'tcx>, PositiveCapability>,
}

impl<'a, 'tcx> CapabilityRule<'a, 'tcx> {
    pub fn new(
        pre: CapabilityConstraint<'a>,
        post: HashMap<Place<'tcx>, PositiveCapability>,
    ) -> Self {
        Self { pre, post }
    }
}

pub(crate) enum CapabilityRules<'a, 'tcx> {
    OneOf(IndexVec<Decision, CapabilityRule<'a, 'tcx>>),
}

impl<'a, 'tcx> CapabilityRules<'a, 'tcx> {
    pub(crate) fn one_of(rules: Vec<CapabilityRule<'a, 'tcx>>) -> Self {
        Self::OneOf(IndexVec::from_iter(rules))
    }
}

impl<'a, 'tcx> SymbolicCapabilityCtxt<'a, 'tcx> {
    pub(crate) fn require(&self, constraint: CapabilityConstraint<'a>) {
        self.constraints.borrow_mut().0.insert(constraint);
    }

    pub(crate) fn new(arena: PcgArena<'a>) -> Self {
        Self {
            constraints: arena.alloc(RefCell::new(SymbolicCapabilityConstraints(
                HashSet::default(),
            ))),
            vars: arena.alloc(RefCell::new(CapabilityVars(vec![]))),
            choices: arena.alloc(RefCell::new(Choices::new())),
        }
    }

    pub(crate) fn add_choice(&self, choice: Choice) -> ChoiceIdx {
        self.choices.borrow_mut().add_choice(choice)
    }

    pub(crate) fn introduce_var(
        &self,
        place: Place<'tcx>,
        location: SnapshotLocation,
    ) -> CapabilityVar {
        pcg_validity_assert!(
            !self
                .vars
                .borrow()
                .contains(PlaceAtLocation::new(place, location))
        );
        self.vars
            .borrow_mut()
            .insert(PlaceAtLocation::new(place, location))
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, From)]
pub enum SymbolicCapability {
    Concrete(CapabilityKind),
    Variable(CapabilityVar),
}

impl From<PositiveCapability> for SymbolicCapability {
    fn from(cap: PositiveCapability) -> Self {
        SymbolicCapability::Concrete(cap.into_capability_kind())
    }
}

impl SymbolicCapability {
    pub(crate) fn gte<'a>(self, other: impl Into<Self>) -> CapabilityConstraint<'a> {
        CapabilityConstraint::gte(self, other.into())
    }

    pub(crate) fn expect_positive(self) -> PositiveCapability {
        self.as_positive().unwrap()
    }

    pub(crate) fn as_positive(self) -> Option<PositiveCapability> {
        self.expect_concrete().as_positive()
    }
}

mod private {
    use crate::pcg::{CapabilityKind, PositiveCapability};

    pub trait CapabilityLike<NoCapability = ()>:
        std::fmt::Debug
        + Copy
        + PartialEq
        + From<PositiveCapability>
        + From<CapabilityKind<NoCapability>>
        + 'static
    {
        type Minimum: std::fmt::Debug = Self;
        fn expect_concrete(self) -> CapabilityKind;
        fn minimum<C>(self, other: Self, _ctxt: C) -> Self::Minimum;
    }
}

pub(crate) use private::*;

impl CapabilityLike for CapabilityKind {
    fn expect_concrete(self) -> CapabilityKind {
        self
    }

    fn minimum<C>(self, other: Self, _ctxt: C) -> Self {
        if self <= other {
            self
        } else if other < self {
            other
        } else {
            CapabilityKind::None(())
        }
    }
}

impl From<PositiveCapability> for CapabilityKind {
    fn from(cap: PositiveCapability) -> Self {
        cap.into_capability_kind()
    }
}

impl CapabilityLike<!> for CapabilityKind<!> {
    type Minimum = Option<Self>;
    fn expect_concrete(self) -> CapabilityKind {
        self.into_capability_kind()
    }
    fn minimum<C>(self, other: Self, ctxt: C) -> Self::Minimum {
        self.into_capability_kind()
            .minimum(other.into_capability_kind(), ctxt)
            .as_positive()
    }
}

impl CapabilityLike for SymbolicCapability {
    fn expect_concrete(self) -> CapabilityKind {
        match self {
            SymbolicCapability::Concrete(c) => c,
            SymbolicCapability::Variable(_) => panic!("Expected concrete capability"),
        }
    }
    fn minimum<C>(self, other: Self, ctxt: C) -> Self::Minimum {
        self.expect_concrete()
            .minimum(other.expect_concrete(), ctxt)
            .into()
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

pub type PositiveCapability = CapabilityKind<!>;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "type-export", derive(specta::Type))]
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

impl PartialEq<PositiveCapability> for CapabilityKind {
    fn eq(&self, other: &PositiveCapability) -> bool {
        self.as_positive() == Some(*other)
    }
}

impl PartialOrd<PositiveCapability> for CapabilityKind {
    fn partial_cmp(&self, other: &PositiveCapability) -> Option<Ordering> {
        let Some(positive) = self.as_positive() else {
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
            (Exclusive, _) => Some(Ordering::Greater),
            (ShallowExclusive, Exclusive) => Some(Ordering::Less),
            (ShallowExclusive, Write | CapabilityKind::None(_)) => Some(Ordering::Greater),
            (Write, ShallowExclusive | Exclusive) => Some(Ordering::Less),
            (Read, CapabilityKind::None(_)) => Some(Ordering::Greater),
            (Read, CapabilityKind::Exclusive) => Some(Ordering::Less),
            (CapabilityKind::None(_), _) => Some(Ordering::Less),
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
    pub(crate) fn as_positive(self) -> Option<PositiveCapability> {
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
