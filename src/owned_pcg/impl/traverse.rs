use std::marker::PhantomData;

use crate::{
    RepackType,
    error::PcgInternalError,
    owned_pcg::{
        ExpandedPlace, OwnedExpansion, OwnedPcgInternalNode, OwnedPcgLeafNode, RepackOp,
        node::OwnedPcgNode, node_data::RealData,
    },
    pcg::{OwnedCapability, edge::EdgeMutability},
    rustc_interface::middle::mir::PlaceElem,
    utils::{CompilerCtxt, HasCompilerCtxt, OwnedPlace, Place, data_structures::HashSet},
};

pub(crate) trait TraverseTypes {
    type Err: std::fmt::Debug + From<PcgInternalError> = PcgInternalError;
    type Result;
    type LeafResult = Self::Result;
    type Aggregate = Vec<Self::Result>;
    type BeforeInternalData = ();

    fn empty_aggregate() -> Self::Aggregate;
}

#[allow(clippy::trivially_copy_pass_by_ref)]
pub(crate) trait TraverseComputation<'src, 'tcx>: TraverseTypes {
    fn lift_leaf(node_result: Self::LeafResult) -> Self::Result;

    fn compute_leaf(
        &mut self,
        place: OwnedPlace<'tcx>,
        node: &OwnedPcgLeafNode<'tcx>,
    ) -> ComputeLeafResult<Self>;

    fn start_internal(
        &mut self,
        place: OwnedPlace<'tcx>,
        node: &OwnedPcgInternalNode<'tcx>,
    ) -> StartInternalResult<Self>;

    fn compute_internal(
        &mut self,
        place: OwnedPlace<'tcx>,
        node: &OwnedPcgInternalNode<'tcx>,
        pre: Self::BeforeInternalData,
        ancestor_results: Self::Aggregate,
    ) -> ComputeInternalResult<Self>;

    fn merge(lhs: Self::Aggregate, place: Place<'tcx>, rhs: Self::Result) -> Self::Aggregate;
}

pub(crate) struct GetAllPlaces<'tcx>(PhantomData<&'tcx ()>);

impl GetAllPlaces<'_> {
    pub(crate) fn new() -> Self {
        Self(PhantomData)
    }
}

impl<'tcx> TraverseTypes for GetAllPlaces<'tcx> {
    type Result = HashSet<OwnedPlace<'tcx>>;
    type LeafResult = OwnedPlace<'tcx>;
    type Aggregate = HashSet<OwnedPlace<'tcx>>;

    type Err = PcgInternalError;

    type BeforeInternalData = ();

    fn empty_aggregate() -> Self::Aggregate {
        HashSet::default()
    }
}

impl<'tcx> TraverseComputation<'_, 'tcx> for GetAllPlaces<'tcx> {
    fn lift_leaf(node_result: Self::LeafResult) -> Self::Result {
        std::iter::once(node_result).collect()
    }

    fn compute_leaf(
        &mut self,
        place: OwnedPlace<'tcx>,
        _node: &OwnedPcgLeafNode<'tcx>,
    ) -> ComputeLeafResult<Self> {
        TraverseResult::continue_(place)
    }

    fn compute_internal(
        &mut self,
        place: OwnedPlace<'tcx>,
        _node: &OwnedPcgInternalNode<'tcx>,
        _pre: Self::BeforeInternalData,
        mut desc_results: Self::Aggregate,
    ) -> ComputeInternalResult<Self> {
        desc_results.insert(place);
        TraverseResult::continue_(desc_results)
    }

    fn merge(mut lhs: Self::Aggregate, _place: Place<'tcx>, rhs: Self::Result) -> Self::Aggregate {
        lhs.extend(rhs);
        lhs
    }

    fn start_internal(
        &mut self,
        _place: OwnedPlace<'tcx>,
        _node: &OwnedPcgInternalNode<'tcx>,
    ) -> StartInternalResult<Self> {
        TraverseResult::continue_(())
    }
}

pub(crate) struct GetLeafPlaces<'tcx>(PhantomData<&'tcx ()>);

impl GetLeafPlaces<'_> {
    pub(crate) fn new() -> Self {
        Self(PhantomData)
    }
}

impl<'tcx> TraverseTypes for GetLeafPlaces<'tcx> {
    type Result = HashSet<Place<'tcx>>;
    type LeafResult = Place<'tcx>;
    type Aggregate = HashSet<Place<'tcx>>;

    type Err = PcgInternalError;

    type BeforeInternalData = ();

    fn empty_aggregate() -> Self::Aggregate {
        HashSet::default()
    }
}

impl<'tcx> TraverseComputation<'_, 'tcx> for GetLeafPlaces<'tcx> {
    fn lift_leaf(node_result: Self::LeafResult) -> Self::Result {
        std::iter::once(node_result).collect()
    }

    fn compute_leaf(
        &mut self,
        place: OwnedPlace<'tcx>,
        _node: &OwnedPcgLeafNode<'tcx>,
    ) -> ComputeLeafResult<Self> {
        TraverseResult::continue_(place.place())
    }

    fn compute_internal(
        &mut self,
        _place: OwnedPlace<'tcx>,
        _node: &OwnedPcgInternalNode<'tcx>,
        _pre: Self::BeforeInternalData,
        desc_results: Self::Aggregate,
    ) -> ComputeInternalResult<Self> {
        TraverseResult::continue_(desc_results)
    }

    fn start_internal(
        &mut self,
        _place: OwnedPlace<'tcx>,
        _node: &OwnedPcgInternalNode<'tcx>,
    ) -> StartInternalResult<Self> {
        TraverseResult::continue_(())
    }

    fn merge(mut lhs: Self::Aggregate, _place: Place<'tcx>, rhs: Self::Result) -> Self::Aggregate {
        lhs.extend(rhs);
        lhs
    }
}

pub(crate) struct GetExpansions<'tcx>(PhantomData<&'tcx ()>);

impl GetExpansions<'_> {
    pub(crate) fn new() -> Self {
        Self(PhantomData)
    }
}

impl<'tcx> TraverseTypes for GetExpansions<'tcx> {
    type Result = HashSet<ExpandedPlace<'tcx>>;
    type LeafResult = ();
    type Aggregate = HashSet<ExpandedPlace<'tcx>>;

    type Err = PcgInternalError;

    type BeforeInternalData = ();

    fn empty_aggregate() -> Self::Aggregate {
        HashSet::default()
    }
}

impl<'tcx> TraverseComputation<'_, 'tcx> for GetExpansions<'tcx> {
    fn compute_leaf(
        &mut self,
        _place: OwnedPlace<'tcx>,
        _node: &OwnedPcgLeafNode<'tcx>,
    ) -> ComputeLeafResult<Self> {
        TraverseResult::continue_(())
    }

    fn compute_internal(
        &mut self,
        place: OwnedPlace<'tcx>,
        node: &OwnedPcgInternalNode<'tcx>,
        _pre: Self::BeforeInternalData,
        mut descendant_results: Self::Aggregate,
    ) -> ComputeInternalResult<Self> {
        descendant_results.insert(ExpandedPlace::new(place.place(), node.expansion.without_data()));
        TraverseResult::continue_(descendant_results)
    }

    fn start_internal(
        &mut self,
        _place: OwnedPlace<'tcx>,
        _node: &OwnedPcgInternalNode<'tcx>,
    ) -> StartInternalResult<Self> {
        TraverseResult::continue_(())
    }

    fn lift_leaf(_node_result: Self::LeafResult) -> Self::Result {
        HashSet::default()
    }

    fn merge(mut lhs: Self::Aggregate, _place: Place<'tcx>, rhs: Self::Result) -> Self::Aggregate {
        lhs.extend(rhs);
        lhs
    }
}

pub(crate) trait Traversable<'src, 'tcx: 'src> {
    fn traverse<'a: 'src, T: TraverseComputation<'src, 'tcx> + 'src + 'a>(
        &self,
        place: OwnedPlace<'tcx>,
        computation: &mut T,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> TraverseResult<T::Result, T::Result, T::Result, T::Err>
    where
        'tcx: 'a;

    fn traverse_result<'a: 'src, T: TraverseComputation<'src, 'tcx> + 'src + 'a>(
        &self,
        place: OwnedPlace<'tcx>,
        computation: &mut T,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Result<T::Result, T::Err>
    where
        'tcx: 'a,
    {
        match self.traverse(place, computation, ctxt) {
            TraverseResult::Continue(result) => Ok(result),
            TraverseResult::LocalShortCircuit(lc) => Ok(lc),
            TraverseResult::GlobalShortCircuit(sc) => Ok(sc),
            TraverseResult::Error(err) => Err(err),
        }
    }

    fn check_initialization<'a: 'src>(
        &self,
        place: OwnedPlace<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Result<CheckInitializationState<'tcx>, PcgInternalError>
    where
        'tcx: 'a,
    {
        let mut state = CheckInitializationState::new();
        self.traverse_result(place, &mut state, ctxt)?;
        Ok(state)
    }
}

pub(crate) enum TraverseResult<C, LS, GS, E> {
    Continue(C),
    LocalShortCircuit(LS),
    GlobalShortCircuit(GS),
    Error(E),
}

pub(crate) type ComputeLeafResult<T> = TraverseResult<
    <T as TraverseTypes>::LeafResult,
    <T as TraverseTypes>::Result,
    <T as TraverseTypes>::Result,
    <T as TraverseTypes>::Err,
>;

pub(crate) type StartInternalResult<T> = TraverseResult<
    <T as TraverseTypes>::BeforeInternalData,
    <T as TraverseTypes>::Result,
    <T as TraverseTypes>::Result,
    <T as TraverseTypes>::Err,
>;

pub(crate) type ComputeInternalResult<T> = TraverseResult<
    <T as TraverseTypes>::Result,
    !,
    <T as TraverseTypes>::Result,
    <T as TraverseTypes>::Err,
>;

impl<C, LS, GS, E> TraverseResult<C, LS, GS, E> {
    pub(crate) fn local_short_circuit(result: LS) -> Self {
        TraverseResult::LocalShortCircuit(result)
    }
    pub(crate) fn continue_(result: C) -> Self {
        TraverseResult::Continue(result)
    }

    pub(crate) fn global_short_circuit(result: GS) -> Self {
        TraverseResult::GlobalShortCircuit(result)
    }

    pub(crate) fn error(err: E) -> Self {
        TraverseResult::Error(err)
    }
}

impl<'src, 'tcx: 'src> Traversable<'src, 'tcx> for OwnedPcgInternalNode<'tcx> {
    fn traverse<'a: 'src, T: TraverseComputation<'src, 'tcx> + 'a>(
        &self,
        place: OwnedPlace<'tcx>,
        computation: &mut T,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> TraverseResult<T::Result, T::Result, T::Result, T::Err>
    where
        'tcx: 'a,
    {
        let pre = match computation.start_internal(place, self) {
            TraverseResult::Continue(pre_result) => pre_result,
            TraverseResult::GlobalShortCircuit(sc) => {
                return TraverseResult::global_short_circuit(sc);
            }
            TraverseResult::Error(err) => return TraverseResult::error(err),
            TraverseResult::LocalShortCircuit(lc) => {
                return TraverseResult::local_short_circuit(lc);
            }
        };
        let mut agg = T::empty_aggregate();
        for (child_place, node) in self.expansion.child_nodes(place.place(), ctxt) {
            let child_owned = child_place.as_owned_place(ctxt).unwrap();
            let child_result = match node.traverse(child_owned, computation, ctxt) {
                TraverseResult::LocalShortCircuit(result) | TraverseResult::Continue(result) => {
                    result
                }
                TraverseResult::GlobalShortCircuit(sc) => {
                    return TraverseResult::global_short_circuit(sc);
                }
                TraverseResult::Error(err) => return TraverseResult::error(err),
            };
            agg = T::merge(agg, child_place, child_result);
        }
        match computation.compute_internal(place, self, pre, agg) {
            TraverseResult::Continue(result) => TraverseResult::continue_(result),
            TraverseResult::GlobalShortCircuit(sc) => TraverseResult::global_short_circuit(sc),
            TraverseResult::Error(err) => TraverseResult::error(err),
        }
    }
}

impl<'src, 'tcx: 'src> Traversable<'src, 'tcx> for OwnedPcgNode<'tcx> {
    fn traverse<'a: 'src, T: TraverseComputation<'src, 'tcx> + 'a>(
        &self,
        place: OwnedPlace<'tcx>,
        computation: &mut T,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> TraverseResult<T::Result, T::Result, T::Result, T::Err>
    where
        'tcx: 'a,
    {
        match self {
            OwnedPcgNode::Leaf(owned_pcg_leaf_node) => {
                match computation.compute_leaf(place, owned_pcg_leaf_node) {
                    TraverseResult::Continue(result) => {
                        TraverseResult::continue_(T::lift_leaf(result))
                    }
                    TraverseResult::LocalShortCircuit(lc) => {
                        TraverseResult::local_short_circuit(lc)
                    }
                    TraverseResult::GlobalShortCircuit(sc) => {
                        TraverseResult::global_short_circuit(sc)
                    }
                    TraverseResult::Error(err) => TraverseResult::error(err),
                }
            }
            OwnedPcgNode::Internal(internal) => internal.traverse(place, computation, ctxt),
        }
    }
}
pub(crate) struct RepackOpsToExpandFrom<'src, 'a, 'tcx> {
    pub(crate) _base_inherent_capability: OwnedCapability,
    pub(crate) ctxt: CompilerCtxt<'a, 'tcx, ()>,
    _marker: PhantomData<&'src ()>,
}

impl<'a, 'tcx> RepackOpsToExpandFrom<'_, 'a, 'tcx> {
    pub(crate) fn new(
        base_inherent_capability: OwnedCapability,
        ctxt: CompilerCtxt<'a, 'tcx, ()>,
    ) -> Self {
        Self {
            _base_inherent_capability: base_inherent_capability,
            ctxt,
            _marker: PhantomData,
        }
    }
}

pub(crate) struct ExpandFrom<'tcx> {
    pub(crate) node: OwnedPcgNode<'tcx>,
    pub(crate) ops: Vec<RepackOp<'tcx>>,
}

impl<'tcx> ExpandFrom<'tcx> {
    fn new(node: OwnedPcgNode<'tcx>, ops: Vec<RepackOp<'tcx>>) -> Self {
        Self { node, ops }
    }
    fn leaf(place: OwnedPlace<'tcx>, node: OwnedPcgLeafNode<'tcx>) -> Self {
        let ops = if OwnedCapability::Deep > node.capability {
            vec![RepackOp::weaken(
                place,
                OwnedCapability::Deep,
                node.capability,
            )]
        } else {
            vec![]
        };
        Self {
            node: OwnedPcgNode::Leaf(node),
            ops,
        }
    }
}

impl<'tcx> TraverseTypes for RepackOpsToExpandFrom<'_, '_, 'tcx> {
    type Result = ExpandFrom<'tcx>;
    type LeafResult = ExpandFrom<'tcx>;
    type Aggregate = (
        Vec<RepackOp<'tcx>>,
        Vec<(PlaceElem<'tcx>, OwnedPcgNode<'tcx>)>,
    );

    type Err = PcgInternalError;

    type BeforeInternalData = CheckInitializationState<'tcx>;

    fn empty_aggregate() -> Self::Aggregate {
        (vec![], vec![])
    }
}

impl<'a, 'tcx: 'a> TraverseComputation<'_, 'tcx> for RepackOpsToExpandFrom<'_, 'a, 'tcx> {
    fn lift_leaf(node_result: Self::LeafResult) -> Self::Result {
        node_result
    }

    fn compute_leaf(
        &mut self,
        place: OwnedPlace<'tcx>,
        node: &OwnedPcgLeafNode<'tcx>,
    ) -> ComputeLeafResult<Self> {
        TraverseResult::continue_(ExpandFrom::leaf(place, *node))
    }

    fn start_internal(
        &mut self,
        place: OwnedPlace<'tcx>,
        node: &OwnedPcgInternalNode<'tcx>,
    ) -> StartInternalResult<Self> {
        if place.is_enum(self.ctxt) {
            return TraverseResult::local_short_circuit(ExpandFrom::leaf(
                place,
                OwnedPcgLeafNode::new(OwnedCapability::Uninitialized),
            ));
        }
        TraverseResult::continue_(node.check_initialization(place, self.ctxt).unwrap())
    }

    fn compute_internal(
        &mut self,
        place: OwnedPlace<'tcx>,
        node: &OwnedPcgInternalNode<'tcx>,
        pre: Self::BeforeInternalData,
        desc_results: Self::Aggregate,
    ) -> ComputeInternalResult<Self> {
        let _edge_mutability = if pre.is_fully_initialized() {
            EdgeMutability::Immutable
        } else {
            EdgeMutability::Mutable
        };
        let (ops, result_map) = desc_results;
        let mut new_ops = vec![RepackOp::expand(
            place.place(),
            node.expansion.guide(),
            RepackType::Real,
            self.ctxt,
        )];
        new_ops.extend(ops);
        let node = OwnedPcgNode::Internal(OwnedPcgInternalNode::new(OwnedExpansion::from_vec(
            result_map,
        )));
        TraverseResult::continue_(ExpandFrom::new(node, new_ops))
    }

    fn merge(lhs: Self::Aggregate, place: Place<'tcx>, rhs: Self::Result) -> Self::Aggregate {
        let (mut ops, mut expansions) = lhs;
        ops.extend(rhs.ops);
        expansions.push((place.last_projection().unwrap().1, rhs.node));
        (ops, expansions)
    }
}

impl TraverseTypes for CheckInitializationState<'_> {
    type Result = bool;

    type Err = PcgInternalError;

    type LeafResult = Self::Result;

    type Aggregate = ();

    type BeforeInternalData = ();

    fn empty_aggregate() -> Self::Aggregate {}
}

#[allow(dead_code)]
pub(crate) enum CheckInitializationState<'tcx> {
    AllInitialized(HashSet<Place<'tcx>>),
    Uninitialized(Place<'tcx>),
}

impl<'tcx> CheckInitializationState<'tcx> {
    pub(crate) fn new() -> Self {
        Self::AllInitialized(HashSet::default())
    }

    pub(crate) fn is_fully_initialized(&self) -> bool {
        matches!(self, Self::AllInitialized(_))
    }

    pub(crate) fn as_all_initialized(&self) -> Option<&HashSet<Place<'tcx>>> {
        match self {
            Self::AllInitialized(places) => Some(places),
            Self::Uninitialized(_) => None,
        }
    }

    pub(crate) fn mark_initialized(&mut self, place: Place<'tcx>) {
        match self {
            Self::AllInitialized(places) => {
                places.insert(place);
            }
            Self::Uninitialized(_) => unreachable!(),
        }
    }

    pub(crate) fn mark_uninitialized(&mut self, place: Place<'tcx>) {
        *self = Self::Uninitialized(place);
    }
}

impl<'tcx> TraverseComputation<'_, 'tcx> for CheckInitializationState<'tcx> {
    fn compute_leaf(
        &mut self,
        place: OwnedPlace<'tcx>,
        node: &OwnedPcgLeafNode<'tcx>,
    ) -> ComputeLeafResult<Self> {
        if node.capability.is_deep() {
            self.mark_initialized(place.place());
            TraverseResult::continue_(true)
        } else {
            self.mark_uninitialized(place.place());
            TraverseResult::global_short_circuit(false)
        }
    }

    fn compute_internal(
        &mut self,
        _place: OwnedPlace<'tcx>,
        _node: &OwnedPcgInternalNode<'tcx>,
        _pre: Self::BeforeInternalData,
        _ancestor_results: Self::Aggregate,
    ) -> ComputeInternalResult<Self> {
        TraverseResult::continue_(true)
    }

    fn lift_leaf(node_result: Self::LeafResult) -> Self::Result {
        node_result
    }

    fn start_internal(
        &mut self,
        _place: OwnedPlace<'tcx>,
        _node: &OwnedPcgInternalNode<'tcx>,
    ) -> StartInternalResult<Self> {
        TraverseResult::continue_(())
    }

    fn merge(_lhs: Self::Aggregate, _place: Place<'tcx>, _rhs: Self::Result) -> Self::Aggregate {}
}

pub(crate) struct FindSubtreeResult<'pcg, 'tcx> {
    path_from_root: Vec<&'pcg OwnedPcgInternalNode<'tcx>>,
    subtree: Option<&'pcg OwnedPcgNode<'tcx, RealData>>,
}

impl<'pcg, 'tcx> FindSubtreeResult<'pcg, 'tcx> {
    pub(crate) fn new() -> Self {
        Self {
            path_from_root: vec![],
            subtree: None,
        }
    }

    pub(crate) fn none() -> Self {
        Self {
            path_from_root: vec![],
            subtree: None,
        }
    }

    pub(crate) fn push_to_path(&mut self, node: &'pcg OwnedPcgInternalNode<'tcx>) {
        self.path_from_root.push(node);
    }

    pub(crate) fn set_subtree(&mut self, subtree: &'pcg OwnedPcgNode<'tcx, RealData>) {
        self.subtree = Some(subtree);
    }

    pub(crate) fn subtree(&self) -> Option<&'pcg OwnedPcgNode<'tcx, RealData>> {
        self.subtree
    }

    pub(crate) fn parent_node(&self) -> Option<&'pcg OwnedPcgInternalNode<'tcx>> {
        self.subtree?;
        self.path_from_root.last().copied()
    }
}
