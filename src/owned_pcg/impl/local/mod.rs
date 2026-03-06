// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub(crate) mod join;

use std::{
    cmp::Reverse,
    fmt::{Debug, Formatter, Result},
};

use crate::{
    borrow_pcg::graph::BorrowsGraph,
    error::PcgUnsupportedError,
    owned_pcg::{
        RepackCollapse, RepackExpand, RepackGuide,
        node::{OwnedPcgInternalNode, OwnedPcgLeafNode, OwnedPcgNode},
        node_data::{self, NodeData},
        traverse::{
            ExpandFrom, FindSubtreeResult, GetAllPlaces, GetExpansions, GetLeafPlaces,
            RepackOpsToExpandFrom, Traversable,
        },
    },
    pcg::OwnedCapability,
    rustc_interface::middle::mir::{self, PlaceElem},
    utils::{
        DebugCtxt, HasCompilerCtxt, OwnedPlace, Place, PlaceLike, data_structures::HashSet, place::PlaceExpansion
    },
};
use derive_more::{Deref, DerefMut};
use itertools::Itertools;

use crate::{owned_pcg::RepackOp, utils::CompilerCtxt};

#[derive(Clone, PartialEq, Eq)]
/// The permissions of a local, each key in the hashmap is a "root" projection of the local
/// Examples of root projections are: `_1`, `*_1.f`, `*(*_.f).g` (i.e. either a local or a deref)
pub enum OwnedPcgLocal<'tcx> {
    Unallocated,
    Allocated(LocalExpansions<'tcx>),
}

impl Debug for OwnedPcgLocal<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::Unallocated => write!(f, "U"),
            Self::Allocated(cps) => write!(f, "{cps:?}"),
        }
    }
}

impl<'tcx> OwnedPcgLocal<'tcx> {
    pub(crate) fn check_validity(
        &self,
        borrows: &BorrowsGraph<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> std::result::Result<(), String> {
        match self {
            Self::Unallocated => Ok(()),
            Self::Allocated(cps) => cps.check_validity(borrows, ctxt),
        }
    }
    pub fn get_allocated(&self) -> &LocalExpansions<'tcx> {
        match self {
            Self::Allocated(cps) => cps,
            Self::Unallocated => panic!("Expected allocated local"),
        }
    }
    pub fn get_allocated_mut(&mut self) -> &mut LocalExpansions<'tcx> {
        match self {
            Self::Allocated(cps) => cps,
            Self::Unallocated => panic!("Expected allocated local"),
        }
    }
    pub(crate) fn new(capability: OwnedCapability) -> Self {
        Self::Allocated(LocalExpansions::new(OwnedPcgNode::leaf(capability)))
    }
    pub fn is_unallocated(&self) -> bool {
        matches!(self, Self::Unallocated)
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub(crate) struct ExpandedPlace<'tcx, P = Place<'tcx>, D = ()> {
    pub(crate) place: P,
    pub(crate) expansion: PlaceExpansion<'tcx, D>,
}

impl<'tcx, D> ExpandedPlace<'tcx, Place<'tcx>, D> {
    pub(crate) fn new(place: Place<'tcx>, expansion: PlaceExpansion<'tcx, D>) -> Self {
        Self { place, expansion }
    }
}

impl ExpandedPlace<'_> {
    pub(crate) fn guide(&self) -> RepackGuide {
        self.expansion.guide()
    }
}

impl<'tcx, P> ExpandedPlace<'tcx, P> {
    pub(crate) fn expansion_places<Ctxt>(
        &self,
        ctxt: Ctxt,
    ) -> std::result::Result<HashSet<P>, PcgUnsupportedError<'tcx>>
    where
        P: PlaceLike<'tcx, Ctxt>,
    {
        Ok(self
            .place
            .expansion_places(&self.expansion, ctxt)?
            .into_iter()
            .collect())
    }
}

#[derive(Deref, DerefMut, Clone, PartialEq, Eq, Debug)]
pub struct LocalExpansions<'tcx> {
    root: OwnedPcgNode<'tcx>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ApplyCollapseError {
    NoSubtree,
}

impl<'tcx> LocalExpansions<'tcx> {
    pub(crate) fn places(
        &self,
        local: mir::Local,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> HashSet<OwnedPlace<'tcx>> {
        self.root
            .traverse_result(OwnedPlace::from(local), &mut GetAllPlaces::new(), ctxt)
            .unwrap()
    }

    pub(crate) fn new(root: OwnedPcgNode<'tcx>) -> Self {
        Self { root }
    }

    pub(crate) fn apply_collapse<'a, Ctxt: HasCompilerCtxt<'a, 'tcx> + DebugCtxt>(
        &mut self,
        collapse: RepackCollapse<'tcx>,
        ctxt: Ctxt,
    ) -> std::result::Result<(), ApplyCollapseError>
    where
        'tcx: 'a,
    {
        let subtree = self
            .subtree_mut(collapse.to.projection)
            .ok_or(ApplyCollapseError::NoSubtree)?;
        subtree.collapse(collapse.to, ctxt);
        Ok(())
    }

    pub(crate) fn perform_expand_action<'a, Ctxt: HasCompilerCtxt<'a, 'tcx>>(
        &mut self,
        expand: RepackExpand<'tcx>,
        ctxt: Ctxt,
    ) where
        'tcx: 'a,
    {
        let subtree = self.subtree_mut(expand.from.projection).unwrap();
        let expansion = OwnedExpansion::from_repack_expand(expand, ctxt);
        match subtree {
            OwnedPcgNode::Leaf(_leaf) => {
                *subtree = OwnedPcgNode::Internal(OwnedPcgInternalNode::new(expansion));
            }
            OwnedPcgNode::Internal(_internal) => {
                unreachable!(
                    "Expected leaf node, but found internal node when expanding {:?} -> {:?}",
                    expand.from, expand.guide
                );
            }
        }
    }

    pub(crate) fn join<'a>(
        &mut self,
        local: mir::Local,
        other: &mut Self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Vec<RepackOp<'tcx>>
    where
        'tcx: 'a,
    {
        self.root.join(local.into(), &mut other.root, ctxt)
    }

    pub(crate) fn expansions_shortest_first<'a>(
        &self,
        local: mir::Local,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Vec<ExpandedPlace<'tcx>>
    where
        'tcx: 'a,
    {
        self.traverse_result(OwnedPlace::from(local), &mut GetExpansions::new(), ctxt)
            .unwrap()
            .into_iter()
            .sorted_by_key(|e| Reverse(e.place.projection.len()))
            .collect()
    }
}

impl<'tcx, D: NodeData<'tcx>> OwnedPcgNode<'tcx, D> {
    pub(crate) fn as_leaf_node(&self) -> Option<&OwnedPcgLeafNode<'tcx, D>> {
        match self {
            Self::Leaf(leaf) => Some(leaf),
            Self::Internal(_) => None,
        }
    }
}

impl<'tcx> OwnedPcgNode<'tcx> {
    #[allow(clippy::needless_pass_by_value)]
    pub(crate) fn insert_expansion(
        &mut self,
        projection: &[mir::PlaceElem<'tcx>],
        expansion: PlaceExpansion<'tcx>,
    ) {
        let tree = self.subtree_mut(projection).unwrap();
        match tree {
            OwnedPcgNode::Leaf(leaf) => {
                *self = OwnedPcgNode::Internal(OwnedPcgInternalNode::new(OwnedExpansion::new(
                    expansion.map_data(|()| OwnedPcgNode::Leaf(*leaf)),
                )));
            }
            OwnedPcgNode::Internal(_) => todo!(),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Deref, DerefMut)]
pub struct OwnedExpansion<'tcx, IData: NodeData<'tcx> = node_data::RealData> {
    pub(crate) expansion: PlaceExpansion<'tcx, IData::Data>,
}

impl<'tcx> OwnedExpansion<'tcx> {
    pub(crate) fn from_vec(expansions: Vec<(PlaceElem<'tcx>, OwnedPcgNode<'tcx>)>) -> Self {
        Self::new(PlaceExpansion::from_vec(expansions))
    }
    pub(crate) fn from_repack_expand<'a>(
        expand: RepackExpand<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Self
    where
        'tcx: 'a,
    {
        let expansion = expand
            .from
            .expansion(expand.guide, ctxt)
            .map_data(|()| OwnedPcgNode::Leaf(OwnedPcgLeafNode::new(OwnedCapability::Deep)));
        Self::new(expansion)
    }
}

pub(crate) struct LeafOwnedExpansion<'tcx> {
    pub(crate) base_place: Place<'tcx>,
    _expansion: OwnedExpansion<'tcx, node_data::Shallow<OwnedCapability>>,
}

impl<'tcx> LeafOwnedExpansion<'tcx> {
    pub(crate) fn new(
        base_place: Place<'tcx>,
        expansion: OwnedExpansion<'tcx, node_data::Shallow<OwnedCapability>>,
    ) -> Self {
        Self {
            base_place,
            _expansion: expansion,
        }
    }
}

impl<'tcx, IData: NodeData<'tcx>> OwnedExpansion<'tcx, IData> {
    pub(crate) fn new(expansion: PlaceExpansion<'tcx, IData::Data>) -> Self {
        Self { expansion }
    }
}

impl<'tcx> OwnedExpansion<'tcx> {
    pub(crate) fn leaf_expansions<'a>(
        &self,
        base_place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Vec<LeafOwnedExpansion<'tcx>>
    where
        'tcx: 'a,
    {
        if let Some(le) = self.as_leaf_expansion(base_place) {
            return vec![le];
        }
        let mut result = vec![];
        for (elem, data) in self.expansion.data() {
            let place = base_place.project_elem(elem, ctxt).unwrap();
            result.extend(data.leaf_expansions(place, ctxt));
        }
        result
    }

    pub(crate) fn as_leaf_expansion(
        &self,
        base_place: Place<'tcx>,
    ) -> Option<LeafOwnedExpansion<'tcx>> {
        let expansion = OwnedExpansion::new(
            self.expansion
                .try_map_data(|d| d.as_leaf_node().map(|l| l.capability))?,
        );
        Some(LeafOwnedExpansion::new(base_place, expansion))
    }
}

impl<'tcx, D> PlaceExpansion<'tcx, D> {
    pub(crate) fn child_nodes<'a>(
        &self,
        base_place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> impl Iterator<Item = (Place<'tcx>, &D)>
    where
        'tcx: 'a,
    {
        self.data().into_iter().map(move |(elem, data)| {
            let place = base_place.project_elem(elem, ctxt).unwrap();
            (place, data)
        })
    }

    pub(crate) fn child<'a>(&self, elem: mir::PlaceElem<'tcx>) -> Option<&D>
    where
        'tcx: 'a,
    {
        self.elems_data()
            .into_iter()
            .find(|(e, _)| *e == elem)
            .and_then(|(_, data)| data)
    }

    pub(crate) fn child_mut<'a>(&mut self, elem: mir::PlaceElem<'tcx>) -> Option<&mut D>
    where
        'tcx: 'a,
    {
        self.elems_data_mut()
            .into_iter()
            .find(|(e, _)| *e == elem)
            .and_then(|(_, data)| data)
    }

    pub(crate) fn data<'slf>(&'slf self) -> Vec<(mir::PlaceElem<'tcx>, &'slf D)> {
        self.map_elems_data(|d| d, |d| d)
    }
}

impl<'tcx> OwnedExpansion<'tcx> {
    pub(crate) fn collapse<'a>(
        &mut self,
        base_place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> CollapseResult<'tcx>
    where
        'tcx: 'a,
    {
        let mut result = CollapseResult::empty();
        for (elem, elem_data) in self.expansion.elems_data_mut() {
            if let Some(data) = elem_data {
                let place = base_place.project_elem(elem, ctxt).unwrap();
                // First recurse into any internal children
                if let Some(collapse_result) = data.collapse(place, ctxt) {
                    result.join(collapse_result);
                }
                // Incorporate this child's capability (whether it was
                // already a leaf or just became one after recursive collapse)
                if let Some(cap) = data.owned_capability() {
                    result.incorporate_child_capability(cap);
                }
            }
        }
        result.ops.push(RepackOp::Collapse(RepackCollapse::new(
            base_place,
            result.result_capability.into(),
            self.expansion.guide(),
        )));
        result
    }
}

pub(crate) struct CollapseResult<'tcx> {
    result_capability: OwnedCapability,
    pub(crate) ops: Vec<RepackOp<'tcx>>,
}

impl CollapseResult<'_> {
    fn empty() -> Self {
        Self {
            result_capability: OwnedCapability::Deep,
            ops: vec![],
        }
    }

    fn join(&mut self, other: Self) {
        self.incorporate_child_capability(other.result_capability);
        self.ops.extend(other.ops);
    }

    fn incorporate_child_capability(&mut self, cap: OwnedCapability) {
        if cap < self.result_capability {
            self.result_capability = cap;
        }
    }
}

impl<'tcx> OwnedPcgNode<'tcx> {
    pub(crate) fn join<'a>(
        &mut self,
        base_place: OwnedPlace<'tcx>,
        other: &mut OwnedPcgNode<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Vec<RepackOp<'tcx>>
    where
        'tcx: 'a,
    {
        if self == other {
            return vec![];
        }
        match (&mut *self, other) {
            (OwnedPcgNode::Leaf(leaf), OwnedPcgNode::Leaf(other_leaf)) => {
                if leaf.capability < other_leaf.capability {
                    // For enum places with Write capability, keep the minimum.
                    // Write on an enum indicates a prior enum expansion/collapse
                    // (e.g., from a match arm that moved fields), which permanently
                    // lowers the capability. Taking MAX here would incorrectly
                    // upgrade back to Exclusive from a path that didn't expand.
                    if leaf.capability == OwnedCapability::Uninitialized
                        && base_place.is_enum(ctxt)
                    {
                        other_leaf.capability = leaf.capability;
                        return vec![];
                    }
                    let result = vec![RepackOp::weaken(
                        base_place,
                        other_leaf.capability,
                        leaf.capability,
                    )];
                    leaf.capability = other_leaf.capability;
                    return result;
                } else if leaf.capability > other_leaf.capability {
                    // Symmetric: if other has Write on an enum, keep Write
                    if other_leaf.capability == OwnedCapability::Uninitialized
                        && base_place.is_enum(ctxt)
                    {
                        leaf.capability = other_leaf.capability;
                        return vec![];
                    }
                    other_leaf.capability = leaf.capability;
                }
                vec![]
            }
            (OwnedPcgNode::Internal(internal), OwnedPcgNode::Leaf(_other_leaf)) => {
                if internal.expansion.is_enum_expansion() {
                    let collapse_result = internal.collapse(base_place.place(), ctxt);
                    let ops = collapse_result.ops;
                    // Enum expansions collapse to Write capability
                    // (matches RepackOpsToExpandFrom::start_internal behavior)
                    *self = OwnedPcgNode::leaf(OwnedCapability::Uninitialized);
                    ops
                } else {
                    vec![]
                }
            }
            (OwnedPcgNode::Leaf(leaf), other) => {
                let result =
                    other.repack_ops_to_expand_from(base_place, leaf.capability, ctxt);
                *self = result.node;
                // eprintln!("ops: {}", ops.display_string(ctxt));
                result.ops
            }
            (OwnedPcgNode::Internal(internal), OwnedPcgNode::Internal(other)) => {
                let mut result = vec![];
                for (child_proj, child_data) in internal.expansion.elems_data_mut() {
                    let Some(child_data) = child_data else {
                        continue;
                    };
                    if let Some(other_child_data) = other.expansion.child_mut(child_proj) {
                        let child_place = base_place
                            .project_elem(child_proj, ctxt)
                            .unwrap()
                            .as_owned_place(ctxt)
                            .unwrap();
                        result.extend(child_data.join(
                            child_place,
                            other_child_data,
                            ctxt,
                        ));
                    }
                }
                result
            }
        }
    }

    pub(crate) fn repack_ops_to_expand_from<'a>(
        &self,
        base_place: OwnedPlace<'tcx>,
        base_inherent_capability: OwnedCapability,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> ExpandFrom<'tcx>
    where
        'tcx: 'a,
    {
        self.traverse_result(
            base_place,
            &mut RepackOpsToExpandFrom::new(base_inherent_capability, ctxt.ctxt()),
            ctxt,
        )
        .unwrap()
    }

    pub(crate) fn leaf_expansions<'a>(
        &self,
        base_place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Vec<LeafOwnedExpansion<'tcx>>
    where
        'tcx: 'a,
    {
        let OwnedPcgNode::Internal(internal) = self else {
            return vec![];
        };
        internal.leaf_expansions(base_place, ctxt)
    }

    pub(crate) fn collapse<'a>(
        &mut self,
        base_place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Option<CollapseResult<'tcx>>
    where
        'tcx: 'a,
    {
        match self {
            OwnedPcgNode::Leaf(_) => None,
            OwnedPcgNode::Internal(internal) => {
                let result = internal.collapse(base_place, ctxt);
                *self = OwnedPcgNode::leaf(result.result_capability);
                Some(result)
            }
        }
    }
    pub(crate) fn subtree_mut<'slf>(
        &'slf mut self,
        projection: &[mir::PlaceElem<'tcx>],
    ) -> Option<&'slf mut Self> {
        if projection.is_empty() {
            return Some(self);
        }
        let internal = self.as_internal_mut()?;
        for (elem, elem_data) in internal.elems_data_mut() {
            if projection[0] != elem {
                continue;
            }
            let remaining_projection = &projection[1..];
            if let Some(data) = elem_data {
                return data.subtree_mut(remaining_projection);
            }
        }
        None
    }

    pub(crate) fn find_subtree<'slf>(
        &'slf self,
        projection: &[mir::PlaceElem<'tcx>],
    ) -> FindSubtreeResult<'slf, 'tcx> {
        let mut result = FindSubtreeResult::new();
        if projection.is_empty() {
            result.set_subtree(self);
            return result;
        }
        let mut current = self;
        for proj in projection {
            let OwnedPcgNode::Internal(internal) = current else {
                return result;
            };
            result.push_to_path(internal);
            let Some(child) = internal.expansion.child(*proj) else {
                return FindSubtreeResult::none();
            };
            current = child;
        }
        result.set_subtree(current);
        result
    }

    pub(crate) fn contains_projection_to(&self, projection: &[mir::PlaceElem<'tcx>]) -> bool {
        self.find_subtree(projection).subtree().is_some()
    }

    pub(crate) fn leaf_places<'a>(
        &self,
        base_place: OwnedPlace<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> HashSet<Place<'tcx>>
    where
        'tcx: 'a,
    {
        self.traverse_result(base_place, &mut GetLeafPlaces::new(), ctxt)
            .unwrap()
    }

    pub(crate) fn all_places<'a>(
        &self,
        base_place: OwnedPlace<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> HashSet<OwnedPlace<'tcx>>
    where
        'tcx: 'a,
    {
        self.traverse_result(base_place, &mut GetAllPlaces::new(), ctxt)
            .unwrap()
    }

    #[allow(clippy::unused_self, clippy::unnecessary_wraps)]
    pub(crate) fn check_validity(
        &self,
        _borrows: &BorrowsGraph<'tcx>,
        _ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> std::result::Result<(), String> {
        Ok(())
    }
}
