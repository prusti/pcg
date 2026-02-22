use std::{
    marker::PhantomData,
    ops::{ControlFlow, FromResidual, Try},
};

use crate::{
    error::PcgInternalError,
    owned_pcg::{
        ExpandedPlace, OwnedPcgInternalNode, OwnedPcgLeafNode, RepackOp,
        node::OwnedPcgNode,
        node_data::{Deep, DeepRef, FromData, InternalData, Shallow},
    },
    pcg::{OwnedCapability, Pcg, edge::EdgeMutability},
    rustc_interface::ast::Mutability,
    utils::{CompilerCtxt, HasCompilerCtxt, Place, data_structures::HashSet},
};

pub(crate) trait TraverseComputation<'src, 'tcx> {
    type Err: std::fmt::Debug + From<PcgInternalError> = PcgInternalError;
    type NodeResult;
    type AggregateResult;
    fn lift(node_result: Self::NodeResult) -> Self::AggregateResult;

    fn lift_result(
        result: TraverseResult<Self::NodeResult, Self::Err, Self::AggregateResult>,
    ) -> TraverseResult<Self::AggregateResult, Self::Err> {
        match result {
            TraverseResult::Continue(result) => TraverseResult::Continue(Self::lift(result)),
            TraverseResult::Break(residual) => TraverseResult::Break(residual),
        }
    }

    fn compute_leaf(
        &mut self,
        place: Place<'tcx>,
        node: &OwnedPcgLeafNode<'tcx>,
    ) -> TraverseResult<Self::NodeResult, Self::Err, Self::AggregateResult>;

    fn compute_internal(
        &mut self,
        place: Place<'tcx>,
        node: &OwnedPcgInternalNode<'tcx>,
    ) -> TraverseResult<Self::NodeResult, Self::Err, Self::AggregateResult>;

    fn fold(
        &mut self,
        acc: Self::AggregateResult,
        rhs: Self::AggregateResult,
    ) -> TraverseResult<Self::AggregateResult, Self::Err>;
}

pub(crate) struct GetAllPlaces;

impl<'src, 'tcx> TraverseComputation<'src, 'tcx> for GetAllPlaces {
    type AggregateResult = HashSet<Place<'tcx>>;
    type NodeResult = Place<'tcx>;
    fn lift(node_result: Self::NodeResult) -> Self::AggregateResult {
        std::iter::once(node_result).collect()
    }

    fn compute_leaf(
        &mut self,
        place: Place<'tcx>,
        _node: &OwnedPcgLeafNode<'tcx>,
    ) -> TraverseResult<Self::NodeResult, Self::Err, Self::AggregateResult> {
        TraverseResult::Continue(place)
    }

    fn compute_internal(
        &mut self,
        place: Place<'tcx>,
        _node: &OwnedPcgInternalNode<'tcx>,
    ) -> TraverseResult<Self::NodeResult, Self::Err, Self::AggregateResult> {
        TraverseResult::Continue(place)
    }

    fn fold(
        &mut self,
        mut acc: Self::AggregateResult,
        rhs: Self::AggregateResult,
    ) -> TraverseResult<Self::AggregateResult, Self::Err> {
        acc.extend(rhs);
        TraverseResult::Continue(acc)
    }
}

pub(crate) struct GetLeafPlaces;

impl<'src, 'tcx> TraverseComputation<'src, 'tcx> for GetLeafPlaces {
    type AggregateResult = HashSet<Place<'tcx>>;
    type NodeResult = Option<Place<'tcx>>;
    fn lift(node_result: Self::NodeResult) -> Self::AggregateResult {
        if let Some(place) = node_result {
            std::iter::once(place).collect()
        } else {
            HashSet::default()
        }
    }

    fn compute_leaf(
        &mut self,
        place: Place<'tcx>,
        node: &OwnedPcgLeafNode<'tcx>,
    ) -> TraverseResult<Self::NodeResult, Self::Err, Self::AggregateResult> {
        TraverseResult::Continue(Some(place))
    }

    fn compute_internal(
        &mut self,
        _place: Place<'tcx>,
        _node: &OwnedPcgInternalNode<'tcx>,
    ) -> TraverseResult<Self::NodeResult, Self::Err, Self::AggregateResult> {
        TraverseResult::Continue(None)
    }

    fn fold(
        &mut self,
        mut acc: Self::AggregateResult,
        rhs: Self::AggregateResult,
    ) -> TraverseResult<Self::AggregateResult, Self::Err> {
        acc.extend(rhs);
        TraverseResult::Continue(acc)
    }
}

pub(crate) struct GetExpansions;

impl<'src, 'tcx> TraverseComputation<'src, 'tcx> for GetExpansions {
    type AggregateResult = HashSet<ExpandedPlace<'tcx>>;
    type NodeResult = HashSet<ExpandedPlace<'tcx>>;
    fn lift(node_result: Self::NodeResult) -> Self::AggregateResult {
        node_result
    }

    fn compute_leaf(
        &mut self,
        _place: Place<'tcx>,
        _node: &OwnedPcgLeafNode<'tcx>,
    ) -> TraverseResult<Self::NodeResult, Self::Err, Self::AggregateResult> {
        TraverseResult::Continue(HashSet::default())
    }

    fn compute_internal(
        &mut self,
        place: Place<'tcx>,
        node: &OwnedPcgInternalNode<'tcx>,
    ) -> TraverseResult<Self::NodeResult, Self::Err, Self::AggregateResult> {
        TraverseResult::Continue(node.expanded_places(place))
    }

    fn fold(
        &mut self,
        mut acc: Self::AggregateResult,
        rhs: Self::AggregateResult,
    ) -> TraverseResult<Self::AggregateResult, Self::Err> {
        acc.extend(rhs);
        TraverseResult::Continue(acc)
    }
}

pub(crate) trait Traversable<'src, 'tcx: 'src> {
    fn traverse_result<'a, T: TraverseComputation<'src, 'tcx>>(
        &self,
        place: Place<'tcx>,
        computation: &mut T,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> TraverseResult<T::AggregateResult, T::Err>
    where
        'tcx: 'a;

    fn traverse<'a: 'src, T: TraverseComputation<'src, 'tcx> + 'src>(
        &self,
        place: Place<'tcx>,
        computation: &mut T,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Result<T::AggregateResult, T::Err>
    where
        'tcx: 'a,
    {
        self.traverse_result(place, computation, ctxt).result()
    }

    fn check_initialization<'a: 'src>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Result<CheckInitializationState<'tcx>, PcgInternalError>
    where
        'tcx: 'a,
    {
        let mut state = CheckInitializationState::new();
        self.traverse(place, &mut state, ctxt)?;
        Ok(state)
    }
}

pub(crate) enum TraverseBreak<T, E> {
    Error(E),
    ShortCircuit(T),
}

pub(crate) enum TraverseResult<T, E, S = T> {
    Continue(T),
    Break(TraverseBreak<S, E>),
}

impl<T, E, S> TraverseResult<T, E, S> {
    pub(crate) fn short_circuit(result: S) -> Self {
        TraverseResult::Break(TraverseBreak::ShortCircuit(result))
    }
    pub(crate) fn from_result<EE: Into<E>>(result: Result<T, EE>) -> Self {
        match result {
            Ok(result) => TraverseResult::Continue(result),
            Err(error) => TraverseResult::Break(TraverseBreak::Error(error.into())),
        }
    }
}
impl<T, E> TraverseResult<T, E> {
    pub(crate) fn result(self) -> Result<T, E> {
        match self {
            TraverseResult::Continue(result)
            | TraverseResult::Break(TraverseBreak::ShortCircuit(result)) => Ok(result),
            TraverseResult::Break(TraverseBreak::Error(error)) => Err(error),
        }
    }
}
impl<T, E, S> FromResidual<TraverseBreak<S, E>> for TraverseResult<T, E, S> {
    fn from_residual(residual: TraverseBreak<S, E>) -> Self {
        TraverseResult::Break(residual)
    }
}

impl<T, E, S> Try for TraverseResult<T, E, S> {
    type Output = T;
    type Residual = TraverseBreak<S, E>;
    fn from_output(output: Self::Output) -> Self {
        TraverseResult::Continue(output)
    }

    fn branch(self) -> ControlFlow<Self::Residual, Self::Output> {
        match self {
            TraverseResult::Continue(output) => ControlFlow::Continue(output),
            TraverseResult::Break(residual) => ControlFlow::Break(residual),
        }
    }
}
impl<'src, 'tcx: 'src> Traversable<'src, 'tcx> for OwnedPcgInternalNode<'tcx> {
    fn traverse_result<'a, T: TraverseComputation<'src, 'tcx>>(
        &self,
        place: Place<'tcx>,
        computation: &mut T,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> TraverseResult<T::AggregateResult, T::Err>
    where
        'tcx: 'a,
    {
        let root_result = computation.compute_internal(place, self);
        let mut result = T::lift_result(root_result)?;
        for expansion in self.expansions() {
            for (place, node) in expansion.child_nodes(place, ctxt) {
                let child_result = node.traverse_result(place, computation, ctxt)?;
                result = computation.fold(result, child_result)?;
            }
        }
        TraverseResult::Continue(result)
    }
}

impl<'src, 'tcx: 'src> Traversable<'src, 'tcx> for OwnedPcgNode<'tcx> {
    fn traverse_result<'a, T: TraverseComputation<'src, 'tcx>>(
        &self,
        place: Place<'tcx>,
        computation: &mut T,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> TraverseResult<T::AggregateResult, T::Err>
    where
        'tcx: 'a,
    {
        match self {
            OwnedPcgNode::Leaf(owned_pcg_leaf_node) => {
                T::lift_result(computation.compute_leaf(place, owned_pcg_leaf_node))
            }
            OwnedPcgNode::Internal(internal) => internal.traverse_result(place, computation, ctxt),
        }
    }
}
pub(crate) struct RepackOpsToExpandFrom<'src, 'a, 'tcx> {
    pub(crate) base_inherent_capability: OwnedCapability,
    pub(crate) ctxt: CompilerCtxt<'a, 'tcx, ()>,
    _marker: PhantomData<&'src ()>,
}

impl<'src, 'a, 'tcx> RepackOpsToExpandFrom<'src, 'a, 'tcx> {
    pub(crate) fn new(
        base_inherent_capability: OwnedCapability,
        ctxt: CompilerCtxt<'a, 'tcx, ()>,
    ) -> Self {
        Self {
            base_inherent_capability,
            ctxt,
            _marker: PhantomData,
        }
    }
}

impl<'src, 'a: 'src, 'tcx: 'a> TraverseComputation<'src, 'tcx>
    for RepackOpsToExpandFrom<'src, 'a, 'tcx>
{
    type AggregateResult = Vec<RepackOp<'tcx>>;
    type NodeResult = Vec<RepackOp<'tcx>>;
    fn lift(node_result: Self::NodeResult) -> Self::AggregateResult {
        node_result
    }

    fn compute_leaf(
        &mut self,
        place: Place<'tcx>,
        node: &OwnedPcgLeafNode<'tcx>,
    ) -> TraverseResult<Self::NodeResult, Self::Err, Self::AggregateResult> {
        let result = if node.inherent_capability < self.base_inherent_capability {
            vec![RepackOp::weaken(
                place,
                self.base_inherent_capability.into(),
                node.inherent_capability.into(),
            )]
        } else {
            vec![]
        };
        TraverseResult::Continue(result)
    }

    fn compute_internal(
        &mut self,
        place: Place<'tcx>,
        node: &OwnedPcgInternalNode<'tcx>,
    ) -> TraverseResult<Self::NodeResult, Self::Err, Self::AggregateResult> {
        let edge_mutability = if !node
            .check_initialization(place, self.ctxt)
            .unwrap()
            .is_fully_initialized()
        {
            EdgeMutability::Mutable
        } else {
            EdgeMutability::Immutable
        };
        let result = node
            .expansions_with_guides()
            .map(|(guide, e)| {
                RepackOp::expand(place, guide, edge_mutability, self.ctxt)
            })
            .collect::<Vec<_>>();
        TraverseResult::Continue(result)
    }

    fn fold(
        &mut self,
        mut acc: Self::AggregateResult,
        rhs: Self::AggregateResult,
    ) -> TraverseResult<Self::AggregateResult, Self::Err> {
        acc.extend(rhs);
        TraverseResult::Continue(acc)
    }
}

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

impl<'src, 'tcx> TraverseComputation<'src, 'tcx> for CheckInitializationState<'tcx> {
    type AggregateResult = bool;
    type NodeResult = bool;
    fn lift(node_result: Self::NodeResult) -> Self::AggregateResult {
        node_result
    }

    fn compute_leaf(
        &mut self,
        place: Place<'tcx>,
        node: &OwnedPcgLeafNode<'tcx>,
    ) -> TraverseResult<Self::NodeResult, Self::Err, Self::AggregateResult> {
        if node.inherent_capability.is_deep() {
            self.mark_initialized(place);
            TraverseResult::Continue(true)
        } else {
            self.mark_uninitialized(place);
            TraverseResult::short_circuit(false)
        }
    }

    fn compute_internal(
        &mut self,
        _place: Place<'tcx>,
        node: &OwnedPcgInternalNode<'tcx>,
    ) -> TraverseResult<Self::NodeResult, Self::Err, Self::AggregateResult> {
        TraverseResult::Continue(true)
    }

    fn fold(
        &mut self,
        acc: Self::AggregateResult,
        rhs: Self::AggregateResult,
    ) -> TraverseResult<Self::AggregateResult, Self::Err> {
        if acc && rhs {
            TraverseResult::Continue(true)
        } else {
            TraverseResult::Break(TraverseBreak::ShortCircuit(false))
        }
    }
}

pub(crate) struct FindSubtreeResult<'pcg, 'tcx> {
    path_from_root: Vec<&'pcg OwnedPcgInternalNode<'tcx>>,
    subtree: Option<&'pcg OwnedPcgNode<'tcx, Deep>>,
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

    pub(crate) fn root_subtree(node: &'pcg OwnedPcgNode<'tcx, Deep>) -> Self {
        Self {
            path_from_root: vec![],
            subtree: Some(node),
        }
    }

    pub(crate) fn push_to_path(&mut self, node: &'pcg OwnedPcgInternalNode<'tcx>) {
        self.path_from_root.push(node);
    }

    pub(crate) fn set_subtree(&mut self, subtree: &'pcg OwnedPcgNode<'tcx, Deep>) {
        self.subtree = Some(subtree);
    }

    pub(crate) fn subtree(&self) -> Option<&'pcg OwnedPcgNode<'tcx, Deep>> {
        self.subtree
    }

    pub(crate) fn parent_node(&self) -> Option<&'pcg OwnedPcgInternalNode<'tcx>> {
        if self.subtree.is_none() {
            return None;
        }
        self.path_from_root.last().copied()
    }
}
