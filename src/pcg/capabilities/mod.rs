pub(crate) mod capability_kind;

pub use capability_kind::*;

use crate::{
    pcg_validity_assert,
    rustc_interface::index::{Idx, IndexVec},
    utils::data_structures::HashMap,
};
use std::cell::RefCell;

use derive_more::From;

use crate::{
    pcg::PcgArena,
    utils::{Place, SnapshotLocation, data_structures::HashSet},
};

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
        self.into_positive().unwrap()
    }

    pub(crate) fn into_positive(self) -> Option<PositiveCapability> {
        self.expect_concrete().into_positive()
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

impl CapabilityLike<!> for CapabilityKind<!> {
    type Minimum = Option<Self>;
    fn expect_concrete(self) -> CapabilityKind {
        self.into_capability_kind()
    }
    fn minimum<C>(self, other: Self, ctxt: C) -> Self::Minimum {
        self.into_capability_kind()
            .minimum(other.into_capability_kind(), ctxt)
            .into_positive()
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
