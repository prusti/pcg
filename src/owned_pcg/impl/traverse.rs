use std::ops::ControlFlow;

use crate::{
    owned_pcg::{
        ExpandedPlace, OwnedPcgInternalNode, OwnedPcgLeafNode, RepackOp,
        node::OwnedPcgNode,
        node_data::{Deep, FromDeep, InternalData, Shallow},
    },
    pcg::{OwnedCapability, edge::EdgeMutability},
    rustc_interface::ast::Mutability,
    utils::{CompilerCtxt, HasCompilerCtxt, Place, data_structures::HashSet},
};

pub(crate) trait TraverseComputation<'tcx> {
    type Depth: FromDeep<'tcx> + InternalData<'tcx> = Shallow;
    type AggregateResult;
    type NodeResult;
    fn lift(&mut self, node_result: Self::NodeResult) -> Self::AggregateResult;
    fn compute(
        &mut self,
        place: Place<'tcx>,
        node: &OwnedPcgNode<'tcx, Self::Depth>,
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

    fn compute(
        &mut self,
        place: Place<'tcx>,
        _node: &OwnedPcgNode<'tcx, Self::Depth>,
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
    fn lift(&mut self, _node_result: Self::NodeResult) -> Self::AggregateResult {
        HashSet::default()
    }

    fn compute(
        &mut self,
        place: Place<'tcx>,
        node: &OwnedPcgNode<'tcx, Self::Depth>,
    ) -> ControlFlow<Self::AggregateResult, Self::NodeResult> {
        if node.is_leaf() {
            ControlFlow::Continue(Some(place))
        } else {
            ControlFlow::Continue(None)
        }
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

    fn compute(
        &mut self,
        place: Place<'tcx>,
        node: &OwnedPcgNode<'tcx, Self::Depth>,
    ) -> ControlFlow<Self::AggregateResult, Self::NodeResult> {
        if let Some(internal) = node.as_internal() {
            ControlFlow::Continue(internal.expanded_places(place))
        } else {
            ControlFlow::Continue(HashSet::default())
        }
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

impl<'tcx> OwnedPcgNode<'tcx> {
    fn traverse_result<'a, T: TraverseComputation<'tcx>>(
        &self,
        place: Place<'tcx>,
        computation: &mut T,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> ControlFlow<T::AggregateResult, T::AggregateResult>
    where
        'tcx: 'a,
    {
        match self {
            OwnedPcgNode::Leaf(owned_pcg_leaf_node) => {
                let result =
                    computation.compute(place, &OwnedPcgNode::Leaf(*owned_pcg_leaf_node))?;
                ControlFlow::Continue(computation.lift(result))
            }
            OwnedPcgNode::Internal(internal) => {
                let root_result = computation.compute(
                    place,
                    &OwnedPcgNode::Internal(T::Depth::from_deep(internal)),
                )?;
                let mut result = computation.lift(root_result);
                for expansion in internal.expansions() {
                    for (place, node) in expansion.child_nodes(place, ctxt) {
                        let child_result = node.traverse_result(place, computation, ctxt)?;
                        result = computation.fold(result, child_result)?;
                    }
                }
                ControlFlow::Continue(result)
            }
        }
    }
    pub(crate) fn traverse<'a, T: TraverseComputation<'tcx>>(
        &self,
        place: Place<'tcx>,
        computation: &mut T,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> T::AggregateResult
    where
        'tcx: 'a,
    {
        match self.traverse_result(place, computation, ctxt) {
            ControlFlow::Continue(result) => result,
            ControlFlow::Break(result) => result,
        }
    }
}

pub(crate) struct RepackOpsToExpandFrom<'a, 'tcx> {
    pub(crate) base_inherent_capability: OwnedCapability,
    pub(crate) is_borrowed: Box<dyn Fn(Place<'tcx>) -> Option<Mutability> + 'a>,
    pub(crate) ctxt: CompilerCtxt<'a, 'tcx, ()>,
}

impl<'a, 'tcx> TraverseComputation<'tcx> for RepackOpsToExpandFrom<'a, 'tcx> {
    type Depth = Deep;
    type AggregateResult = Vec<RepackOp<'tcx>>;
    type NodeResult = Vec<RepackOp<'tcx>>;
    fn lift(&mut self, node_result: Self::NodeResult) -> Self::AggregateResult {
        node_result
    }
    fn compute(
        &mut self,
        place: Place<'tcx>,
        node: &OwnedPcgNode<'tcx, Self::Depth>,
    ) -> ControlFlow<Self::AggregateResult, Self::NodeResult> {
        let result = match node {
            OwnedPcgNode::Leaf(owned_pcg_leaf_node) => {
                if owned_pcg_leaf_node.inherent_capability < self.base_inherent_capability {
                    vec![RepackOp::weaken(
                        place,
                        owned_pcg_leaf_node.inherent_capability.into(),
                        self.base_inherent_capability.into(),
                    )]
                } else {
                    vec![]
                }
            }
            OwnedPcgNode::Internal(expansions) => expansions
                .iter()
                .flat_map(|(_, e)| {
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
                .collect::<Vec<_>>(),
        };
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
    fn compute(
        &mut self,
        _place: Place<'tcx>,
        node: &OwnedPcgNode<'tcx, Self::Depth>,
    ) -> ControlFlow<Self::AggregateResult, Self::NodeResult> {
        if let OwnedPcgNode::Leaf(owned_pcg_leaf_node) = node
            && !self.0(owned_pcg_leaf_node)
        {
            ControlFlow::Break(false)
        } else {
            ControlFlow::Continue(true)
        }
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
}
