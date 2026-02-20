// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub(crate) mod join;

use std::{
    borrow::Cow,
    fmt::{Debug, Formatter, Result},
    marker::PhantomData,
};

use crate::{
    borrow_pcg::{borrow_pcg_expansion::PlaceExpansion, graph::BorrowsGraph},
    error::PcgUnsupportedError,
    owned_pcg::{RepackCollapse, RepackExpand, RepackGuide},
    pcg::{OwnedCapability, PositiveCapability},
    rustc_interface::middle::mir,
    utils::{DebugCtxt, HasCompilerCtxt, PlaceLike, data_structures::HashSet},
};
use derive_more::{Deref, DerefMut};

use crate::{
    owned_pcg::RepackOp,
    utils::{CompilerCtxt, Place, display::DisplayWithCompilerCtxt},
};

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
    pub fn new(capability: OwnedCapability) -> Self {
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
    pub(crate) fn is_enum_expansion(&self) -> bool {
        self.expansion.is_enum_expansion()
    }
    pub(crate) fn guide(&self) -> Option<RepackGuide> {
        self.expansion.guide().copied()
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

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct OwnedPcgLeafNode<'tcx> {
    pub(crate) inherent_capability: OwnedCapability,
    _marker: PhantomData<&'tcx ()>,
}

impl<'tcx> OwnedPcgLeafNode<'tcx> {
    pub(crate) fn new(inherent_capability: OwnedCapability) -> Self {
        Self {
            inherent_capability,
            _marker: PhantomData,
        }
    }
}

pub trait InternalData<'tcx> {
    type Data: Clone + Eq + Debug;
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Deep;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Shallow<T = ()>(PhantomData<T>);

impl<'tcx> InternalData<'tcx> for Deep {
    type Data = OwnedPcgNode<'tcx>;
}

impl<'tcx, T: Clone + Eq + Debug> InternalData<'tcx> for Shallow<T> {
    type Data = T;
}

pub(crate) type ShallowOwnedNode<'tcx> = OwnedPcgNode<'tcx, Shallow>;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum OwnedPcgNode<'tcx, IData: InternalData<'tcx> = Deep> {
    Leaf(OwnedPcgLeafNode<'tcx>),
    Internal(OwnedPcgInternalNode<'tcx, IData>),
}

#[derive(Clone, PartialEq, Eq, Debug, Deref, DerefMut)]
pub struct OwnedPcgInternalNode<'tcx, IData: InternalData<'tcx> = Deep> {
    expansions: Vec<OwnedExpansion<'tcx, IData>>,
}

impl<'tcx, IData: InternalData<'tcx>> OwnedPcgInternalNode<'tcx, IData> {
    pub(crate) fn new(expansions: OwnedExpansion<'tcx, IData>) -> Self {
        Self {
            expansions: vec![expansions],
        }
    }
    pub(crate) fn expansions(&self) -> &Vec<OwnedExpansion<'tcx, IData>> {
        &self.expansions
    }
}

#[derive(Clone, Copy)]
pub(crate) enum TraverseOrder {
    Postorder,
    Preorder,
}

type LeafExpansion<'tcx> = PlaceExpansion<'tcx, OwnedPcgLeafNode<'tcx>>;

impl<'tcx> OwnedPcgInternalNode<'tcx> {
    pub(crate) fn expanded_places(&self, place: Place<'tcx>) -> Vec<ExpandedPlace<'tcx>> {
        self.expansions
            .iter()
            .map(|e| ExpandedPlace::new(place, e.expansion.without_data()))
            .collect()
    }
}

#[derive(Deref, DerefMut, Clone, PartialEq, Eq, Debug)]
pub struct LocalExpansions<'tcx> {
    root: OwnedPcgNode<'tcx>,
}

impl<'tcx> LocalExpansions<'tcx> {
    pub(crate) fn places(
        &self,
        local: mir::Local,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> HashSet<Place<'tcx>> {
        self.root
            .traverse(
                local.into(),
                &|place, _expansion| place,
                TraverseOrder::Postorder,
                ctxt,
            )
            .into_iter()
            .collect()
    }

    pub(crate) fn new(root: OwnedPcgNode<'tcx>) -> Self {
        Self { root }
    }
    pub(crate) fn perform_collapse_action<'a, Ctxt: HasCompilerCtxt<'a, 'tcx> + DebugCtxt>(
        &mut self,
        collapse: RepackCollapse<'tcx>,
        ctxt: Ctxt,
    ) where
        'tcx: 'a,
    {
        let Some(subtree) = self.subtree_mut(&collapse.to.projection) else {
            panic!(
                "Expected subtree at projection {:?}",
                collapse.to.projection
            );
        };
        subtree.collapse(collapse.to, ctxt);
    }

    pub(crate) fn perform_expand_action<'a, Ctxt: HasCompilerCtxt<'a, 'tcx>>(
        &mut self,
        expand: RepackExpand<'tcx>,
        ctxt: Ctxt,
    ) where
        'tcx: 'a,
    {
        let subtree = self.subtree_mut(&expand.from.projection).unwrap();
        match subtree {
            OwnedPcgNode::Leaf(leaf) => {
                let expansion_kind = if expand.capability.is_read() {
                    OwnedExpansionKind::Read
                } else {
                    OwnedExpansionKind::Mutate
                };
                let expansion: PlaceExpansion<'tcx, OwnedPcgNode<'tcx>> = expand
                    .from
                    .expansion(expand.guide, ctxt)
                    .map_data(|_| OwnedPcgNode::Leaf(*leaf));
                let owned_expansion: OwnedExpansion<'tcx, Deep> = OwnedExpansion::new(expansion);
                *subtree = OwnedPcgNode::Internal(OwnedPcgInternalNode::new(owned_expansion));
            }
            OwnedPcgNode::Internal(_) => todo!(),
        }
    }

    pub(crate) fn join<'a>(
        &mut self,
        local: mir::Local,
        other: &mut Self,
        is_borrowed: impl Fn(Place<'tcx>) -> bool,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Vec<RepackOp<'tcx>>
    where
        'tcx: 'a,
    {
        self.root
            .join(local.into(), &mut other.root, is_borrowed, ctxt)
    }

    pub(crate) fn expansions_shortest_first<'a>(
        &self,
        local: mir::Local,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Vec<ExpandedPlace<'tcx>>
    where
        'tcx: 'a,
    {
        self.preorder(
            Place::from(local),
            &|place, node| {
                node.as_internal()
                    .map(|internal| {
                        internal
                            .expansions()
                            .iter()
                            .map(|e| ExpandedPlace::new(place, e.expansion.without_data()))
                            .collect::<Vec<_>>()
                    })
                    .unwrap_or_default()
            },
            ctxt,
        )
        .into_iter()
        .flatten()
        .collect()
    }

    pub(crate) fn places_to_collapse_to_for_obtain_of<'a>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Vec<Place<'tcx>>
    where
        'tcx: 'a,
    {
        if !place.is_owned(ctxt.ctxt()) {
            return vec![];
        }
        let Some(tree) = self.root.subtree(place.projection) else {
            return vec![];
        };
        tree.traverse(
            place,
            &|place, node| if !node.is_leaf() { vec![place] } else { vec![] },
            TraverseOrder::Postorder,
            ctxt,
        )
        .into_iter()
        .flatten()
        .collect()
    }
}

impl<'tcx> OwnedPcgNode<'tcx> {
    pub(crate) fn inherent_capability(&self) -> OwnedCapability {
        self.fold(
            OwnedCapability::Exclusive,
            &|leaf| leaf.inherent_capability,
            &|a, b| if a < b { a } else { b },
        )
    }

    pub(crate) fn as_leaf_node(&self) -> Option<&OwnedPcgLeafNode<'tcx>> {
        match self {
            Self::Leaf(leaf) => Some(leaf),
            Self::Internal(_) => None,
        }
    }

    pub(crate) fn insert_expansion(
        &mut self,
        kind: OwnedExpansionKind,
        projection: &[mir::PlaceElem<'tcx>],
        expansion: PlaceExpansion<'tcx>,
    ) {
        let tree = self.subtree_mut(projection).unwrap();
        match tree {
            OwnedPcgNode::Leaf(leaf) => {
                *self = OwnedPcgNode::Internal(OwnedPcgInternalNode::new(OwnedExpansion::new(
                    expansion.map_data(|_| OwnedPcgNode::Leaf(*leaf)),
                )));
            }
            OwnedPcgNode::Internal(_) => todo!(),
        }
    }

    pub(crate) fn expansions_mut(&mut self) -> Vec<&mut OwnedExpansion<'tcx>> {
        match self {
            Self::Leaf(_) => vec![],
            Self::Internal(internal) => internal.expansions.iter_mut().map(|e| &mut *e).collect(),
        }
    }

    pub(crate) fn preorder<'a, T>(
        &self,
        place: Place<'tcx>,
        f: &impl Fn(Place<'tcx>, ShallowOwnedNode<'tcx>) -> T,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Vec<T>
    where
        'tcx: 'a,
    {
        self.traverse(place, f, TraverseOrder::Preorder, ctxt)
    }

    pub(crate) fn postorder<'a, T>(
        &self,
        place: Place<'tcx>,
        f: &impl Fn(Place<'tcx>, ShallowOwnedNode<'tcx>) -> T,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Vec<T>
    where
        'tcx: 'a,
    {
        self.traverse(place, f, TraverseOrder::Postorder, ctxt)
    }

    pub(crate) fn fold<'a, T>(
        &self,
        base: T,
        f: &impl Fn(&OwnedPcgLeafNode<'tcx>) -> T,
        fold: &impl Fn(T, T) -> T,
    ) -> T {
        match self {
            OwnedPcgNode::Leaf(owned_pcg_leaf_node) => f(owned_pcg_leaf_node),
            OwnedPcgNode::Internal(internal) => {
                let mut result = base;
                for e in internal.expansions.iter() {
                    for (_, elem_data) in e.expansion.data() {
                        result = elem_data.fold(result, f, fold)
                    }
                }
                result
            }
        }
    }

    pub(crate) fn traverse<'a, T>(
        &self,
        place: Place<'tcx>,
        f: &impl Fn(Place<'tcx>, OwnedPcgNode<'tcx, Shallow>) -> T,
        order: TraverseOrder,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Vec<T>
    where
        'tcx: 'a,
    {
        match self {
            OwnedPcgNode::Leaf(owned_pcg_leaf_node) => vec![f(
                place,
                OwnedPcgNode::leaf(owned_pcg_leaf_node.inherent_capability),
            )],
            OwnedPcgNode::Internal(internal) => {
                let mut descendants: Vec<T> = internal
                    .expansions
                    .iter()
                    .flat_map(|e| {
                        e.expansion
                            .data()
                            .iter()
                            .flat_map(|(elem, data)| {
                                let expanded_place = place.project_deeper(*elem, ctxt).unwrap();
                                data.traverse(expanded_place, f, order, ctxt)
                            })
                            .collect::<Vec<_>>()
                    })
                    .collect();
                let mut this_expansion = internal
                    .expansions
                    .iter()
                    .map(|e| f(place, OwnedPcgNode::internal(e.expansion.without_data())))
                    .collect::<Vec<_>>();
                match order {
                    TraverseOrder::Postorder => {
                        descendants.extend(this_expansion);
                        descendants
                    }
                    TraverseOrder::Preorder => {
                        this_expansion.extend(descendants);
                        this_expansion
                    }
                }
            }
        }
    }
}

impl<'tcx, IData: InternalData<'tcx>> OwnedPcgNode<'tcx, IData> {
    pub(crate) fn is_leaf(&self) -> bool {
        matches!(self, Self::Leaf(_))
    }
    pub(crate) fn leaf(inherent_capability: OwnedCapability) -> Self {
        Self::Leaf(OwnedPcgLeafNode::new(inherent_capability))
    }
    pub(crate) fn internal(place_expansion: PlaceExpansion<'tcx, IData::Data>) -> Self {
        Self::Internal(OwnedPcgInternalNode::new(OwnedExpansion::new(
            place_expansion,
        )))
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) enum OwnedExpansionKind {
    Read,
    Mutate,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct OwnedExpansion<'tcx, IData: InternalData<'tcx> = Deep> {
    pub(crate) expansion: PlaceExpansion<'tcx, IData::Data>,
}

pub(crate) struct LeafOwnedExpansion<'tcx> {
    pub(crate) base_place: Place<'tcx>,
    expansion: OwnedExpansion<'tcx, Shallow<OwnedCapability>>,
}

impl<'tcx> LeafOwnedExpansion<'tcx> {
    pub(crate) fn new(
        base_place: Place<'tcx>,
        expansion: OwnedExpansion<'tcx, Shallow<OwnedCapability>>,
    ) -> Self {
        Self {
            base_place,
            expansion,
        }
    }
}

impl<'tcx, IData: InternalData<'tcx>> OwnedExpansion<'tcx, IData> {
    pub(crate) fn new(expansion: PlaceExpansion<'tcx, IData::Data>) -> Self {
        Self { expansion }
    }

    pub(crate) fn without_data(&self) -> OwnedExpansion<'tcx, Shallow> {
        OwnedExpansion::new(self.expansion.without_data())
    }
}

impl<'tcx, IData: InternalData<'tcx>> OwnedPcgNode<'tcx, IData> {
    pub(crate) fn as_internal(&self) -> Option<&OwnedPcgInternalNode<'tcx, IData>> {
        match self {
            Self::Leaf(_) => None,
            Self::Internal(internal) => Some(internal),
        }
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
            let place = base_place.project_deeper(elem, ctxt).unwrap();
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
                .try_map_data(|d| d.as_leaf_node().map(|l| l.inherent_capability))?,
        );
        Some(LeafOwnedExpansion::new(base_place, expansion))
    }

    pub(crate) fn leaf_places<'a>(
        &self,
        base_place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> HashSet<Place<'tcx>>
    where
        'tcx: 'a,
    {
        self.expansion.leaf_places(base_place, ctxt)
    }
}

impl<'tcx> PlaceExpansion<'tcx, OwnedPcgNode<'tcx>> {
    pub(crate) fn data<'slf>(&'slf self) -> Vec<(mir::PlaceElem<'tcx>, &'slf OwnedPcgNode<'tcx>)> {
        self.map_elems_data(|d| d, &|d| d)
    }
    pub(crate) fn leaf_places<'a>(
        &self,
        base_place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> HashSet<Place<'tcx>>
    where
        'tcx: 'a,
    {
        self.data()
            .into_iter()
            .flat_map(|(elem, data)| {
                let place = base_place.project_deeper(elem, ctxt).unwrap();
                data.leaf_places(place, ctxt)
            })
            .collect()
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
            match elem_data {
                Some(data) => {
                    let place = base_place.project_deeper(elem, ctxt).unwrap();
                    if let Some(collapse_result) = data.collapse(place, ctxt) {
                        result.join(collapse_result);
                    }
                }
                None => {}
            }
        }
        result.ops.push(RepackOp::Collapse(RepackCollapse::new(
            base_place,
            result.result_capability.into(),
            self.expansion.guide().map(|g| g.without_data()),
        )));
        result
    }
}

pub(crate) struct CollapseResult<'tcx> {
    result_capability: OwnedCapability,
    pub(crate) ops: Vec<RepackOp<'tcx>>,
}

impl<'tcx> CollapseResult<'tcx> {
    fn join_all(mut results: Vec<Self>) -> Self {
        let mut result = results.pop().unwrap();
        while let Some(other) = results.pop() {
            result.join(other);
        }
        result
    }

    fn new(result_capability: OwnedCapability, ops: Vec<RepackOp<'tcx>>) -> Self {
        Self {
            result_capability,
            ops,
        }
    }

    fn empty() -> Self {
        Self {
            result_capability: OwnedCapability::Exclusive,
            ops: vec![],
        }
    }

    fn join(&mut self, other: Self) {
        if self.result_capability < other.result_capability {
            self.result_capability = other.result_capability;
        }
        self.ops.extend(other.ops);
    }
}

impl<'tcx> OwnedPcgNode<'tcx> {
    pub(crate) fn join<'a>(
        &mut self,
        base_place: Place<'tcx>,
        other: &mut OwnedPcgNode<'tcx>,
        is_borrowed: impl Fn(Place<'tcx>) -> bool,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Vec<RepackOp<'tcx>>
    where
        'tcx: 'a,
    {
        if self == other {
            return vec![];
        }
        match (self, other) {
            (OwnedPcgNode::Leaf(leaf), OwnedPcgNode::Leaf(other_leaf)) => {
                if leaf.inherent_capability < other_leaf.inherent_capability {
                    let mut result = vec![];
                    leaf.inherent_capability = other_leaf.inherent_capability;
                    if !is_borrowed(base_place) {
                        result.push(RepackOp::weaken(
                            base_place,
                            leaf.inherent_capability.into(),
                            other_leaf.inherent_capability.into(),
                        ))
                    };
                    return result;
                } else if leaf.inherent_capability > other_leaf.inherent_capability {
                    other_leaf.inherent_capability = leaf.inherent_capability;
                }
                vec![]
            }
            (OwnedPcgNode::Internal(internal), OwnedPcgNode::Internal(other_internal)) => {
                todo!("Join {:?} and {:?}", internal, other_internal);
            }
            (OwnedPcgNode::Internal(internal), OwnedPcgNode::Leaf(other_leaf)) => {
                vec![]
            }
            (OwnedPcgNode::Leaf(leaf), other) => {
                other.repack_ops_to_expand_from(base_place, leaf.inherent_capability, ctxt)
            }
        }
    }

    pub(crate) fn repack_ops_to_expand_from<'a>(
        &self,
        base_place: Place<'tcx>,
        base_inherent_capability: OwnedCapability,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Vec<RepackOp<'tcx>>
    where
        'tcx: 'a,
    {
        self.traverse(
            base_place,
            &|place, node| match node {
                OwnedPcgNode::Leaf(owned_pcg_leaf_node) => {
                    if owned_pcg_leaf_node.inherent_capability < base_inherent_capability {
                        vec![RepackOp::weaken(
                            place,
                            owned_pcg_leaf_node.inherent_capability.into(),
                            base_inherent_capability.into(),
                        )]
                    } else {
                        vec![]
                    }
                }
                OwnedPcgNode::Internal(expansions) => expansions
                    .iter()
                    .map(|e| {
                        RepackOp::expand(
                            place,
                            e.expansion.guide().copied(),
                            if e.kind == OwnedExpansionKind::Read {
                                PositiveCapability::Read
                            } else {
                                PositiveCapability::Exclusive
                            },
                            ctxt,
                        )
                    })
                    .collect::<Vec<_>>(),
            },
            TraverseOrder::Preorder,
            ctxt,
        )
        .into_iter()
        .flatten()
        .collect()
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
        internal
            .expansions
            .iter()
            .flat_map(|e| e.leaf_expansions(base_place, ctxt))
            .collect()
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
                let ops = internal
                    .expansions
                    .iter_mut()
                    .map(|e| e.collapse(base_place, ctxt))
                    .collect::<Vec<_>>();
                let result = CollapseResult::join_all(ops);
                *self = OwnedPcgNode::leaf(result.result_capability);
                Some(result)
            }
        }
    }
    pub(crate) fn subtree_mut<'slf>(
        &'slf mut self,
        projection: &[mir::PlaceElem<'tcx>],
    ) -> Option<&'slf mut Self> {
        if projection.len() == 0 {
            return Some(self);
        }
        for e in self.expansions_mut() {
            for (elem, elem_data) in e.expansion.elems_data_mut() {
                if projection[0] != elem {
                    continue;
                }
                let remaining_projection = &projection[1..];
                if let Some(data) = elem_data {
                    return data.subtree_mut(remaining_projection);
                }
            }
        }
        None
    }

    pub(crate) fn subtree<'slf>(
        &'slf self,
        projection: &[mir::PlaceElem<'tcx>],
    ) -> Option<&'slf Self> {
        if projection.len() == 0 {
            return Some(self);
        }
        let OwnedPcgNode::Internal(internal) = self else {
            return None;
        };
        for e in internal.expansions.iter() {
            for (elem, elem_data) in e.expansion.data() {
                if projection[0] != elem {
                    continue;
                }
                let remaining_projection = &projection[1..];
                if let Some(subtree) = elem_data.subtree(remaining_projection) {
                    return Some(subtree);
                }
            }
        }
        None
    }

    pub(crate) fn contains_projection_to(&self, projection: &[mir::PlaceElem<'tcx>]) -> bool {
        self.subtree(projection).is_some()
    }

    pub(crate) fn leaf_places<'a>(
        &self,
        base_place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> HashSet<Place<'tcx>>
    where
        'tcx: 'a,
    {
        match self {
            Self::Leaf(_) => vec![base_place].into_iter().collect(),
            Self::Internal(internal) => internal
                .expansions
                .iter()
                .flat_map(|e| e.leaf_places(base_place, ctxt))
                .collect(),
        }
    }
    pub(crate) fn check_validity(
        &self,
        borrows: &BorrowsGraph<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> std::result::Result<(), String> {
        Ok(())
    }

    pub(crate) fn has_expansions(&self) -> bool {
        !self.is_leaf()
    }
}
