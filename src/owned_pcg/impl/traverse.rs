use std::{marker::PhantomData, ops::ControlFlow};

use crate::{
    owned_pcg::{
        ExpandedPlace, OwnedPcgInternalNode, OwnedPcgLeafNode, RepackOp,
        node::OwnedPcgNode,
        node_data::{Deep, DeepRef, FromData, InternalData, Shallow},
    },
    pcg::{OwnedCapability, edge::EdgeMutability},
    rustc_interface::ast::Mutability,
    utils::{CompilerCtxt, HasCompilerCtxt, Place, data_structures::HashSet},
};

pub(crate) trait TraverseComputation<'tcx> {
    type Depth: InternalData<'tcx> = Shallow;
    type AggregateResult;
    type NodeResult;
    fn lift(&mut self, node_result: Self::NodeResult) -> Self::AggregateResult;

    fn compute_leaf<'src>(
        &mut self,
        place: Place<'tcx>,
        node: &'src OwnedPcgLeafNode<'tcx>,
    ) -> ControlFlow<Self::AggregateResult, Self::NodeResult>;

    fn compute_internal(
        &mut self,
        place: Place<'tcx>,
        node: OwnedPcgInternalNode<'tcx, Self::Depth>,
    ) -> ControlFlow<Self::AggregateResult, Self::NodeResult>;

    fn fold(
        &mut self,
        acc: Self::AggregateResult,
        rhs: Self::AggregateResult,
    ) -> ControlFlow<Self::AggregateResult, Self::AggregateResult>;
}

pub(crate) struct GetAllPlaces;

impl<'tcx> TraverseComputation<'tcx> for GetAllPlaces {
    type AggregateResult = HashSet<Place<'tcx>>;
    type NodeResult = Place<'tcx>;
    fn lift(&mut self, node_result: Self::NodeResult) -> Self::AggregateResult {
        std::iter::once(node_result).collect()
    }

    fn compute_leaf(
        &mut self,
        place: Place<'tcx>,
        _node: &OwnedPcgLeafNode<'tcx>,
    ) -> ControlFlow<Self::AggregateResult, Self::NodeResult> {
        ControlFlow::Continue(place)
    }

    fn compute_internal(
        &mut self,
        place: Place<'tcx>,
        _node: OwnedPcgInternalNode<'tcx, Self::Depth>,
    ) -> ControlFlow<Self::AggregateResult, Self::NodeResult> {
        ControlFlow::Continue(place)
    }

    fn fold(
        &mut self,
        mut acc: Self::AggregateResult,
        rhs: Self::AggregateResult,
    ) -> ControlFlow<Self::AggregateResult, Self::AggregateResult> {
        acc.extend(rhs);
        ControlFlow::Continue(acc)
    }
}

pub(crate) struct GetLeafPlaces;

impl<'tcx> TraverseComputation<'tcx> for GetLeafPlaces {
    type AggregateResult = HashSet<Place<'tcx>>;
    type NodeResult = Option<Place<'tcx>>;
    fn lift(&mut self, node_result: Self::NodeResult) -> Self::AggregateResult {
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
    ) -> ControlFlow<Self::AggregateResult, Self::NodeResult> {
        ControlFlow::Continue(Some(place))
    }

    fn compute_internal(
        &mut self,
        _place: Place<'tcx>,
        _node: OwnedPcgInternalNode<'tcx, Self::Depth>,
    ) -> ControlFlow<Self::AggregateResult, Self::NodeResult> {
        ControlFlow::Continue(None)
    }

    fn fold(
        &mut self,
        mut acc: Self::AggregateResult,
        rhs: Self::AggregateResult,
    ) -> ControlFlow<Self::AggregateResult, Self::AggregateResult> {
        acc.extend(rhs);
        ControlFlow::Continue(acc)
    }
}

pub(crate) struct GetExpansions;

impl<'tcx> TraverseComputation<'tcx> for GetExpansions {
    type AggregateResult = HashSet<ExpandedPlace<'tcx>>;
    type NodeResult = HashSet<ExpandedPlace<'tcx>>;
    fn lift(&mut self, node_result: Self::NodeResult) -> Self::AggregateResult {
        node_result
    }

    fn compute_leaf(
        &mut self,
        _place: Place<'tcx>,
        _node: &OwnedPcgLeafNode<'tcx>,
    ) -> ControlFlow<Self::AggregateResult, Self::NodeResult> {
        ControlFlow::Continue(HashSet::default())
    }

    fn compute_internal(
        &mut self,
        place: Place<'tcx>,
        node: OwnedPcgInternalNode<'tcx, Self::Depth>,
    ) -> ControlFlow<Self::AggregateResult, Self::NodeResult> {
        ControlFlow::Continue(node.expanded_places(place))
    }

    fn fold(
        &mut self,
        mut acc: Self::AggregateResult,
        rhs: Self::AggregateResult,
    ) -> ControlFlow<Self::AggregateResult, Self::AggregateResult> {
        acc.extend(rhs);
        ControlFlow::Continue(acc)
    }
}

pub(crate) trait Traversable<'tcx, IData: InternalData<'tcx>> {
    fn traverse_result<'a, 'src, T: TraverseComputation<'tcx> + 'src>(
        &'src self,
        place: Place<'tcx>,
        computation: &mut T,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> ControlFlow<T::AggregateResult, T::AggregateResult>
    where
        'tcx: 'a,
        T::Depth: FromData<'src, 'tcx, IData>;

    fn traverse<'a, 'src, T: TraverseComputation<'tcx> + 'src>(
        &'src self,
        place: Place<'tcx>,
        computation: &mut T,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> T::AggregateResult
    where
        'tcx: 'a,
        T::Depth: FromData<'src, 'tcx, IData>,
    {
        match self.traverse_result(place, computation, ctxt) {
            ControlFlow::Continue(result) => result,
            ControlFlow::Break(result) => result,
        }
    }

    fn is_fully_initialized<'a>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        self.traverse(
            place,
            &mut All(Box::new(|leaf| leaf.inherent_capability.is_deep())),
            ctxt,
        )
    }
}

impl<'tcx, IData: InternalData<'tcx, Data = OwnedPcgNode<'tcx, IData>>> Traversable<'tcx, IData>
    for OwnedPcgInternalNode<'tcx, IData>
{
    fn traverse_result<'a, 'src, T: TraverseComputation<'tcx> + 'src>(
        &'src self,
        place: Place<'tcx>,
        computation: &mut T,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> ControlFlow<T::AggregateResult, T::AggregateResult>
    where
        'tcx: 'a,
        T::Depth: FromData<'src, 'tcx, IData>,
    {
        let root_result = computation.compute_internal(place, T::Depth::from_data(self))?;
        let mut result = computation.lift(root_result);
        for expansion in self.expansions() {
            for (place, node) in expansion.child_nodes(place, ctxt) {
                let child_result = node.traverse_result(place, computation, ctxt)?;
                result = computation.fold(result, child_result)?;
            }
        }
        ControlFlow::Continue(result)
    }
}

impl<'tcx, IData: InternalData<'tcx, Data = OwnedPcgNode<'tcx, IData>>> Traversable<'tcx, IData>
    for OwnedPcgNode<'tcx, IData>
{
    fn traverse_result<'a, 'src, T: TraverseComputation<'tcx> + 'src>(
        &'src self,
        place: Place<'tcx>,
        computation: &mut T,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> ControlFlow<T::AggregateResult, T::AggregateResult>
    where
        'tcx: 'a,
        T::Depth: FromData<'src, 'tcx, IData>,
    {
        match self {
            OwnedPcgNode::Leaf(owned_pcg_leaf_node) => {
                let result = computation.compute_leaf(place, owned_pcg_leaf_node)?;
                ControlFlow::Continue(computation.lift(result))
            }
            OwnedPcgNode::Internal(internal) => internal.traverse_result(place, computation, ctxt),
        }
    }
}

pub(crate) struct RepackOpsToExpandFrom<'src, 'a, 'tcx> {
    pub(crate) base_inherent_capability: OwnedCapability,
    pub(crate) is_borrowed: Box<dyn Fn(Place<'tcx>) -> Option<Mutability> + 'a>,
    pub(crate) ctxt: CompilerCtxt<'a, 'tcx, ()>,
    _marker: PhantomData<&'src ()>,
}

impl<'src, 'a, 'tcx> RepackOpsToExpandFrom<'src, 'a, 'tcx> {
    pub(crate) fn new(
        base_inherent_capability: OwnedCapability,
        is_borrowed: Box<dyn Fn(Place<'tcx>) -> Option<Mutability> + 'a>,
        ctxt: CompilerCtxt<'a, 'tcx, ()>,
    ) -> Self {
        Self {
            base_inherent_capability,
            is_borrowed,
            ctxt,
            _marker: PhantomData,
        }
    }
}

impl<'comp, 'a, 'tcx: 'comp> TraverseComputation<'tcx> for RepackOpsToExpandFrom<'comp, 'a, 'tcx> {
    type Depth = DeepRef<'comp>;
    type AggregateResult = Vec<RepackOp<'tcx>>;
    type NodeResult = Vec<RepackOp<'tcx>>;
    fn lift(&mut self, node_result: Self::NodeResult) -> Self::AggregateResult {
        node_result
    }

    fn compute_leaf(
        &mut self,
        place: Place<'tcx>,
        node: &OwnedPcgLeafNode<'tcx>,
    ) -> ControlFlow<Self::AggregateResult, Self::NodeResult> {
        let result = if node.inherent_capability < self.base_inherent_capability {
            vec![RepackOp::weaken(
                place,
                node.inherent_capability.into(),
                self.base_inherent_capability.into(),
            )]
        } else {
            vec![]
        };
        ControlFlow::Continue(result)
    }

    fn compute_internal(
        &mut self,
        place: Place<'tcx>,
        node: OwnedPcgInternalNode<'tcx, Self::Depth>,
    ) -> ControlFlow<Self::AggregateResult, Self::NodeResult> {
        let result = node
            .expansions()
            .flat_map(|e| {
                e.expansion
                    .child_nodes(place, self.ctxt)
                    .map(|(place, node)| {
                        let edge_mutability = if !node.is_fully_initialized(place, self.ctxt)
                            || matches!((self.is_borrowed)(place), Some(Mutability::Mut))
                        {
                            EdgeMutability::Mutable
                        } else {
                            EdgeMutability::Immutable
                        };
                        RepackOp::expand(place, e.expansion.guide(), edge_mutability, self.ctxt)
                    })
            })
            .collect::<Vec<_>>();
        ControlFlow::Continue(result)
    }

    fn fold(
        &mut self,
        mut acc: Self::AggregateResult,
        rhs: Self::AggregateResult,
    ) -> ControlFlow<Self::AggregateResult, Self::AggregateResult> {
        acc.extend(rhs);
        ControlFlow::Continue(acc)
    }
}

pub(crate) struct All<'tcx>(pub Box<dyn Fn(&OwnedPcgLeafNode<'tcx>) -> bool>);

impl<'tcx> TraverseComputation<'tcx> for All<'tcx> {
    type AggregateResult = bool;
    type NodeResult = bool;
    fn lift(&mut self, node_result: Self::NodeResult) -> Self::AggregateResult {
        node_result
    }

    fn compute_leaf(
        &mut self,
        _place: Place<'tcx>,
        node: &OwnedPcgLeafNode<'tcx>,
    ) -> ControlFlow<Self::AggregateResult, Self::NodeResult> {
        if self.0(node) {
            ControlFlow::Continue(true)
        } else {
            ControlFlow::Break(false)
        }
    }

    fn compute_internal(
        &mut self,
        _place: Place<'tcx>,
        node: OwnedPcgInternalNode<'tcx, Self::Depth>,
    ) -> ControlFlow<Self::AggregateResult, Self::NodeResult> {
        ControlFlow::Continue(true)
    }

    fn fold(
        &mut self,
        acc: Self::AggregateResult,
        rhs: Self::AggregateResult,
    ) -> ControlFlow<Self::AggregateResult, Self::AggregateResult> {
        if acc && rhs {
            ControlFlow::Continue(true)
        } else {
            ControlFlow::Break(false)
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
