//! Per-local owned-place state.
//!
//! This module exposes [`OwnedPcg`], the authoritative source of
//! owned-place information for the PCG. Each allocated local carries
//!
//! 1. An [`InitialisationTree`] recording the [`OwnedCapability`] at
//!    each reachable leaf — the computation target from
//!    <https://prusti.github.io/pcg-docs/computing-place-capabilities.html>.
//! 2. A [`LocalExpansions`] tracking the owned-PCG expansion
//!    structure for this local.

use std::fmt::{Debug, Formatter};

use crate::{
    borrow_pcg::borrow_pcg_expansion::PlaceExpansion,
    owned_pcg::{LocalExpansions, RepackGuide},
    pcg::{
        CapabilityKind,
        owned_state::{InitialisationTree, OwnedCapability},
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesInterface},
    },
    rustc_interface::{
        index::{Idx, IndexVec},
        middle::mir::{self, Local, PlaceElem, ProjectionElem, RETURN_PLACE},
    },
    utils::{
        CompilerCtxt, HasCompilerCtxt, HasLocals, OwnedPlace, Place, PlaceLike, PlaceProjectable,
        data_structures::HashSet,
    },
};

/// Initialisation state for a single local. Either the local is
/// unallocated, or it is allocated and carries both an initialisation
/// tree and the owned-PCG expansion forest rooted at the local.
#[derive(Clone, PartialEq, Eq)]
pub enum LocalInitState<'tcx> {
    Unallocated,
    Allocated {
        tree: InitialisationTree<'tcx>,
        expansions: LocalExpansions<'tcx>,
    },
}

impl Debug for LocalInitState<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unallocated => write!(f, "U"),
            Self::Allocated { expansions, .. } => write!(f, "{expansions:?}"),
        }
    }
}

impl<'tcx> LocalInitState<'tcx> {
    pub(crate) fn new_allocated(local: Local, cap: OwnedCapability) -> Self {
        Self::Allocated {
            tree: InitialisationTree::Leaf(cap),
            expansions: LocalExpansions::new(local),
        }
    }

    pub fn is_allocated(&self) -> bool {
        matches!(self, LocalInitState::Allocated { .. })
    }

    pub fn is_unallocated(&self) -> bool {
        matches!(self, LocalInitState::Unallocated)
    }

    pub fn expansions(&self) -> &LocalExpansions<'tcx> {
        match self {
            Self::Allocated { expansions, .. } => expansions,
            Self::Unallocated => panic!("Expected allocated local"),
        }
    }

    pub fn expansions_mut(&mut self) -> &mut LocalExpansions<'tcx> {
        match self {
            Self::Allocated { expansions, .. } => expansions,
            Self::Unallocated => panic!("Expected allocated local"),
        }
    }

    pub(crate) fn tree(&self) -> Option<&InitialisationTree<'tcx>> {
        match self {
            Self::Allocated { tree, .. } => Some(tree),
            Self::Unallocated => None,
        }
    }

    fn tree_mut(&mut self) -> Option<&mut InitialisationTree<'tcx>> {
        match self {
            Self::Allocated { tree, .. } => Some(tree),
            Self::Unallocated => None,
        }
    }

    pub(crate) fn check_validity(
        &self,
        capabilities: &PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> std::result::Result<(), String> {
        match self {
            Self::Unallocated => Ok(()),
            Self::Allocated { expansions, .. } => expansions.check_validity(capabilities, ctxt),
        }
    }
}

/// Per-body owned-PCG state, indexed by [`Local`]. The
/// initialisation tree and the owned expansion forest live together
/// per-local under [`LocalInitState`].
#[derive(Clone, PartialEq, Eq)]
pub struct OwnedPcg<'tcx> {
    state: IndexVec<Local, LocalInitState<'tcx>>,
}

impl Debug for OwnedPcg<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let v: Vec<_> = self.state.iter().filter(|c| c.is_allocated()).collect();
        v.fmt(f)
    }
}

impl<'tcx> std::ops::Index<Local> for OwnedPcg<'tcx> {
    type Output = LocalInitState<'tcx>;

    fn index(&self, local: Local) -> &Self::Output {
        &self.state[local]
    }
}

impl std::ops::IndexMut<Local> for OwnedPcg<'_> {
    fn index_mut(&mut self, local: Local) -> &mut Self::Output {
        &mut self.state[local]
    }
}

impl<'tcx> OwnedPcg<'tcx> {
    /// Empty shell used by unit tests of the initialisation state. The
    /// resulting value has no locals.
    #[cfg(test)]
    pub(crate) fn empty_for_tests() -> Self {
        Self {
            state: IndexVec::new(),
        }
    }

    pub(crate) fn new(num_locals: usize) -> Self {
        Self {
            state: IndexVec::from_elem_n(LocalInitState::Unallocated, num_locals),
        }
    }

    /// Build the entry state of the start block. Arguments start as
    /// `Deep`, the return place as `Uninit`, and any always-live local
    /// as `Uninit`. Other locals are `Unallocated`.
    pub(crate) fn start_block<
        'a,
        Ctxt: HasLocals,
        C: From<CapabilityKind>,
        P: PlaceLike<'tcx, Ctxt>,
    >(
        capabilities: &mut impl PlaceCapabilitiesInterface<'tcx, C, P>,
        ctxt: Ctxt,
    ) -> Self {
        let always_live = ctxt.always_live_locals();
        let last_arg = Local::from_usize(ctxt.arg_count());
        let state: IndexVec<Local, LocalInitState<'tcx>> = IndexVec::from_fn_n(
            |local: mir::Local| {
                if local == RETURN_PLACE {
                    capabilities.insert(local.into(), CapabilityKind::Write, ctxt);
                    LocalInitState::new_allocated(local, OwnedCapability::Uninit)
                } else if local <= last_arg {
                    capabilities.insert(local.into(), CapabilityKind::Exclusive, ctxt);
                    LocalInitState::new_allocated(local, OwnedCapability::Deep)
                } else if always_live.contains(local) {
                    capabilities.insert(local.into(), CapabilityKind::Write, ctxt);
                    LocalInitState::new_allocated(local, OwnedCapability::Uninit)
                } else {
                    LocalInitState::Unallocated
                }
            },
            ctxt.local_count(),
        );
        Self { state }
    }

    pub(crate) fn check_validity(
        &self,
        capabilities: &PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> std::result::Result<(), String> {
        self.state
            .iter()
            .try_for_each(|c| c.check_validity(capabilities, ctxt))
    }

    pub(crate) fn num_locals(&self) -> usize {
        self.state.len()
    }

    pub(crate) fn is_allocated(&self, local: Local) -> bool {
        self.state
            .get(local)
            .is_some_and(LocalInitState::is_allocated)
    }

    pub(crate) fn allocated_locals(&self) -> Vec<mir::Local> {
        self.state
            .iter_enumerated()
            .filter_map(|(i, c)| c.is_allocated().then_some(i))
            .collect()
    }

    pub(crate) fn unallocated_locals(&self) -> Vec<mir::Local> {
        self.state
            .iter_enumerated()
            .filter_map(|(i, c)| c.is_unallocated().then_some(i))
            .collect()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = &LocalInitState<'tcx>> + '_ {
        self.state.iter()
    }

    pub fn iter_enumerated(&self) -> impl Iterator<Item = (Local, &LocalInitState<'tcx>)> + '_ {
        self.state.iter_enumerated()
    }

    pub(crate) fn leaf_places<'a>(
        &self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> HashSet<OwnedPlace<'tcx>>
    where
        'tcx: 'a,
    {
        self.state
            .iter()
            .filter_map(|c| match c {
                LocalInitState::Allocated { expansions, .. } => Some(expansions),
                LocalInitState::Unallocated => None,
            })
            .flat_map(|e| e.leaf_places(ctxt))
            .collect()
    }

    pub(crate) fn contains_place(&self, place: Place<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        match &self.state[place.local] {
            LocalInitState::Unallocated => false,
            LocalInitState::Allocated { expansions, .. } => expansions.contains_place(place, ctxt),
        }
    }

    /// Allocate `local` with the single root place set to `cap`.
    pub(crate) fn allocate(&mut self, local: Local, cap: OwnedCapability) {
        self.state[local] = LocalInitState::new_allocated(local, cap);
    }

    pub(crate) fn deallocate(&mut self, local: Local) {
        self.state[local] = LocalInitState::Unallocated;
    }

    /// Set the [`OwnedCapability`] of `place` in the tree.
    pub(crate) fn set<'a, Ctxt>(
        &mut self,
        place: OwnedPlace<'tcx>,
        cap: OwnedCapability,
        ctxt: Ctxt,
    ) where
        Ctxt: HasCompilerCtxt<'a, 'tcx>,
        'tcx: 'a,
    {
        let local = place.place().local;
        let projection = place.place().projection;
        let Some(tree) = self.state.get_mut(local).and_then(LocalInitState::tree_mut) else {
            return;
        };
        let root_place: Place<'tcx> = local.into();
        set_cap_at(tree, root_place, projection, cap, ctxt);
    }

    pub(crate) fn remove(&mut self, place: OwnedPlace<'tcx>) {
        if place.place().projection.is_empty()
            && let Some(tree) = self
                .state
                .get_mut(place.place().local)
                .and_then(LocalInitState::tree_mut)
        {
            *tree = InitialisationTree::Leaf(OwnedCapability::Uninit);
        }
    }

    pub(crate) fn remove_strict_postfixes_of(&mut self, place: Place<'tcx>) {
        let Some(tree) = self
            .state
            .get_mut(place.local)
            .and_then(LocalInitState::tree_mut)
        else {
            return;
        };
        let projection = place.projection;
        if projection.is_empty() {
            if let InitialisationTree::Internal(_) = tree {
                *tree = InitialisationTree::Leaf(OwnedCapability::Uninit);
            }
            return;
        }
        collapse_subtree_at(tree, projection);
    }

    pub(crate) fn get(&self, place: OwnedPlace<'tcx>) -> Option<OwnedCapability> {
        let tree = self.state.get(place.place().local)?.tree()?;
        cap_at(tree, place.place().projection)
    }

    pub(crate) fn owned_capability(&self, place: OwnedPlace<'tcx>) -> Option<CapabilityKind> {
        self.get(place).map(OwnedCapability::as_capability_kind)
    }

    /// Pointwise join of the initialisation trees per local.
    pub(crate) fn join_capabilities(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for (local, self_state) in self.state.iter_enumerated_mut() {
            let other_state = other
                .state
                .get(local)
                .cloned()
                .unwrap_or(LocalInitState::Unallocated);
            match (self_state, other_state) {
                (LocalInitState::Unallocated, _) => {}
                (self_s @ LocalInitState::Allocated { .. }, LocalInitState::Unallocated) => {
                    *self_s = LocalInitState::Unallocated;
                    changed = true;
                }
                (
                    LocalInitState::Allocated {
                        tree: self_tree, ..
                    },
                    LocalInitState::Allocated {
                        tree: other_tree, ..
                    },
                ) => {
                    let outcome = self_tree.join(&other_tree);
                    if outcome.changed {
                        *self_tree = outcome.tree;
                        changed = true;
                    }
                }
            }
        }
        changed
    }
}

impl<'tcx> OwnedPcg<'tcx> {
    /// Apply the [`OwnedCapability`] change implied by assigning the
    /// capability kind `cap` to the owned place `place`.
    pub(crate) fn apply_capability_change<'a, Ctxt>(
        &mut self,
        place: OwnedPlace<'tcx>,
        cap: CapabilityKind,
        ctxt: Ctxt,
    ) where
        Ctxt: HasCompilerCtxt<'a, 'tcx>,
        'tcx: 'a,
    {
        match cap {
            CapabilityKind::Exclusive => self.set(place, OwnedCapability::Deep, ctxt),
            CapabilityKind::Write => self.set(place, OwnedCapability::Uninit, ctxt),
            CapabilityKind::ShallowExclusive => self.set(place, OwnedCapability::Shallow, ctxt),
            CapabilityKind::Read => {
                // Read reflects a shared-borrow constraint, not init.
            }
        }
    }

    /// Reset the initialisation tree of `local` to `Leaf(Uninit)` without
    /// deallocating the local.
    pub(crate) fn clear_local(&mut self, local: mir::Local) {
        if let Some(tree) = self.state.get_mut(local).and_then(LocalInitState::tree_mut) {
            *tree = InitialisationTree::Leaf(OwnedCapability::Uninit);
        }
    }
}

fn cap_at<'tcx>(
    mut tree: &InitialisationTree<'tcx>,
    projection: &[PlaceElem<'tcx>],
) -> Option<OwnedCapability> {
    for elem in projection {
        match tree {
            InitialisationTree::Leaf(cap) => return Some(*cap),
            InitialisationTree::Internal(exp) => {
                tree = child(exp, elem)?;
            }
        }
    }
    match tree {
        InitialisationTree::Leaf(cap) => Some(*cap),
        InitialisationTree::Internal(_) => None,
    }
}

fn set_cap_at<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>>(
    tree: &mut InitialisationTree<'tcx>,
    node_place: Place<'tcx>,
    projection: &[PlaceElem<'tcx>],
    cap: OwnedCapability,
    ctxt: Ctxt,
) {
    if projection.is_empty() {
        *tree = InitialisationTree::Leaf(cap);
        return;
    }
    let first = projection[0];
    let Ok(child_place) = node_place.project_deeper(first, ctxt) else {
        return;
    };
    match tree {
        InitialisationTree::Leaf(existing) => {
            if *existing == cap {
                return;
            }
            let existing_cap = *existing;
            let Some(expansion) = expand_leaf(node_place, first, existing_cap, ctxt) else {
                return;
            };
            *tree = InitialisationTree::Internal(expansion);
            if let InitialisationTree::Internal(exp) = tree
                && let Some(sub) = child_mut(exp, &first)
            {
                set_cap_at(sub, child_place, &projection[1..], cap, ctxt);
            }
        }
        InitialisationTree::Internal(exp) => {
            if let Some(sub) = child_mut(exp, &first) {
                set_cap_at(sub, child_place, &projection[1..], cap, ctxt);
            }
        }
    }
    if let InitialisationTree::Internal(exp) = tree
        && let Some(leaf_cap) = uniform_leaf_cap(exp)
    {
        *tree = InitialisationTree::Leaf(leaf_cap);
    }
}

fn uniform_leaf_cap<'tcx>(
    exp: &PlaceExpansion<'tcx, Box<InitialisationTree<'tcx>>>,
) -> Option<OwnedCapability> {
    let children = expansion_children(exp);
    let mut iter = children.into_iter();
    let first = match iter.next()? {
        InitialisationTree::Leaf(cap) => *cap,
        InitialisationTree::Internal(_) => return None,
    };
    for t in iter {
        match t {
            InitialisationTree::Leaf(cap) if *cap == first => {}
            _ => return None,
        }
    }
    Some(first)
}

fn expansion_children<'a, 'tcx>(
    exp: &'a PlaceExpansion<'tcx, Box<InitialisationTree<'tcx>>>,
) -> Vec<&'a InitialisationTree<'tcx>> {
    match exp {
        PlaceExpansion::Fields(fields) => fields.values().map(|(_, t)| t.as_ref()).collect(),
        PlaceExpansion::Deref(t)
        | PlaceExpansion::Guided(
            RepackGuide::Downcast(_, _, t)
            | RepackGuide::ConstantIndex(_, t)
            | RepackGuide::Index(_, t)
            | RepackGuide::Subslice { data: t, .. },
        ) => vec![t.as_ref()],
        PlaceExpansion::Guided(RepackGuide::Default(never)) => match *never {},
    }
}

fn collapse_subtree_at<'tcx>(tree: &mut InitialisationTree<'tcx>, projection: &[PlaceElem<'tcx>]) {
    if projection.is_empty() {
        if let InitialisationTree::Internal(exp) = tree
            && let Some(cap) = uniform_leaf_cap(exp)
        {
            *tree = InitialisationTree::Leaf(cap);
        }
        return;
    }
    let first = projection[0];
    match tree {
        InitialisationTree::Leaf(_) => {}
        InitialisationTree::Internal(exp) => {
            if let Some(sub) = child_mut(exp, &first) {
                collapse_subtree_at(sub, &projection[1..]);
            }
        }
    }
}

fn child<'a, 'tcx>(
    exp: &'a PlaceExpansion<'tcx, Box<InitialisationTree<'tcx>>>,
    elem: &PlaceElem<'tcx>,
) -> Option<&'a InitialisationTree<'tcx>> {
    match (exp, elem) {
        (PlaceExpansion::Fields(fields), PlaceElem::Field(idx, _)) => {
            fields.get(idx).map(|(_, t)| t.as_ref())
        }
        (PlaceExpansion::Deref(d), PlaceElem::Deref) => Some(d.as_ref()),
        _ => None,
    }
}

fn child_mut<'a, 'tcx>(
    exp: &'a mut PlaceExpansion<'tcx, Box<InitialisationTree<'tcx>>>,
    elem: &PlaceElem<'tcx>,
) -> Option<&'a mut InitialisationTree<'tcx>> {
    match (exp, elem) {
        (PlaceExpansion::Fields(fields), PlaceElem::Field(idx, _)) => {
            fields.get_mut(idx).map(|(_, t)| t.as_mut())
        }
        (PlaceExpansion::Deref(d), PlaceElem::Deref) => Some(d.as_mut()),
        _ => None,
    }
}

fn expand_leaf<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>>(
    node_place: Place<'tcx>,
    first: PlaceElem<'tcx>,
    existing_cap: OwnedCapability,
    ctxt: Ctxt,
) -> Option<PlaceExpansion<'tcx, Box<InitialisationTree<'tcx>>>> {
    let leaf = || Box::new(InitialisationTree::Leaf(existing_cap));
    match first {
        ProjectionElem::Field(_idx, _ty) => {
            let siblings = node_place.expand_field(None, ctxt).ok()?;
            let mut fields = std::collections::BTreeMap::new();
            for sib in siblings {
                let Some((_, last)) = sib.last_projection() else {
                    continue;
                };
                if let ProjectionElem::Field(f, ty) = last {
                    fields.insert(f, (ty, leaf()));
                }
            }
            if fields.is_empty() {
                None
            } else {
                Some(PlaceExpansion::Fields(fields))
            }
        }
        ProjectionElem::Deref => Some(PlaceExpansion::Deref(leaf())),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn set_and_get_round_trip_at_root() {
        let mut state = OwnedPcg::new(2);
        let local = Local::from_u32(0);
        state.allocate(local, OwnedCapability::Deep);
        assert_eq!(
            state.get(OwnedPlace::from(local)),
            Some(OwnedCapability::Deep),
        );
    }

    #[test]
    fn join_takes_min_of_entries() {
        let mut a = OwnedPcg::new(2);
        let mut b = OwnedPcg::new(2);
        let local = Local::from_u32(0);
        a.allocate(local, OwnedCapability::Deep);
        b.allocate(local, OwnedCapability::Uninit);
        assert!(a.join_capabilities(&b));
        assert_eq!(
            a.get(OwnedPlace::from(local)),
            Some(OwnedCapability::Uninit),
        );
    }

    #[test]
    fn join_drops_entries_missing_on_one_side() {
        let mut a = OwnedPcg::new(1);
        let b = OwnedPcg::new(1);
        let local = Local::from_u32(0);
        a.allocate(local, OwnedCapability::Deep);
        assert!(a.join_capabilities(&b));
        assert!(!a.is_allocated(local));
    }

    #[test]
    fn owned_capability_matches_mapping() {
        let mut state = OwnedPcg::new(1);
        let local = Local::from_u32(0);
        state.allocate(local, OwnedCapability::Uninit);
        assert_eq!(
            state.owned_capability(OwnedPlace::from(local)),
            Some(CapabilityKind::Write),
        );
    }
}
