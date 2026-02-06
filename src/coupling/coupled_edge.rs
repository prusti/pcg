use derive_more::{Deref, IntoIterator};

use crate::{
    borrow_pcg::{
        AbstractionInputTarget, AbstractionOutputTarget,
        borrow_pcg_edge::{BlockedNode, LocalNode},
        domain::{
            FunctionCallAbstractionInput, FunctionCallAbstractionOutput, LoopAbstractionInput,
            LoopAbstractionOutput,
        },
        edge::abstraction::{
            FunctionCallOrLoop, function::FunctionCallAbstractionEdgeMetadata,
            r#loop::LoopAbstractionEdgeMetadata,
        },
        edge_data::{EdgeData, LabelEdgePlaces, LabelNodePredicate, NodeReplacement},
        graph::Conditioned,
        has_pcs_elem::{LabelPlace, PlaceLabeller},
        validity_conditions::ValidityConditions,
    },
    coupling::{
        CoupledEdgeKind, FunctionCallCoupledEdgeKind, HyperEdge, LoopCoupledEdgeKind,
        PcgCoupledEdgeKind,
    },
    pcg::{PcgNode, PcgNodeLike},
    utils::{
        CompilerCtxt, DebugCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, PcgNodeComponent, PcgPlace,
        data_structures::HashSet,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
    },
};
use std::hash::Hash;

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub enum MaybeCoupled<T, U> {
    Coupled(T),
    NotCoupled(U),
}

impl<Ctxt: Copy, T: DisplayWithCtxt<Ctxt>, U: DisplayWithCtxt<Ctxt>> DisplayWithCtxt<Ctxt>
    for MaybeCoupled<T, U>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        match self {
            MaybeCoupled::Coupled(coupled) => coupled.display_output(ctxt, mode),
            MaybeCoupled::NotCoupled(normal) => normal.display_output(ctxt, mode),
        }
    }
}

pub type MaybeCoupledEdges<'tcx, T> = MaybeCoupled<Box<PcgCoupledEdges<'tcx>>, Vec<T>>;

pub type MaybeCoupledEdgeKind<'tcx, T> = MaybeCoupled<PcgCoupledEdgeKind<'tcx>, T>;

impl<'tcx, Ctxt, P: PcgPlace<'tcx, Ctxt>> EdgeData<'tcx, Ctxt, P> for PcgCoupledEdgeKind<'tcx, P> {
    fn blocked_nodes<'slf>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Box<dyn std::iter::Iterator<Item = BlockedNode<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(self.inputs(ctxt).into_iter().map(|input| input.0))
    }

    fn blocked_by_nodes<'slf>(
        &'slf self,
        _ctxt: Ctxt,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(self.outputs().into_iter().map(|output| output.0))
    }
}

impl<'a, 'tcx, BC: Copy, T: EdgeData<'tcx, CompilerCtxt<'a, 'tcx, BC>>>
    EdgeData<'tcx, CompilerCtxt<'a, 'tcx, BC>> for MaybeCoupledEdgeKind<'tcx, T>
{
    fn blocked_nodes<'slf>(
        &'slf self,
        ctxt: CompilerCtxt<'a, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = crate::pcg::PcgNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        match self {
            MaybeCoupledEdgeKind::Coupled(coupled) => coupled.blocked_nodes(ctxt),
            MaybeCoupledEdgeKind::NotCoupled(normal) => normal.blocked_nodes(ctxt),
        }
    }

    fn blocked_by_nodes<'slf>(
        &'slf self,
        ctxt: CompilerCtxt<'a, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        match self {
            MaybeCoupledEdgeKind::Coupled(coupled) => coupled.blocked_by_nodes(ctxt),
            MaybeCoupledEdgeKind::NotCoupled(normal) => normal.blocked_by_nodes(ctxt),
        }
    }
}

/// The set of coupled edges derived from a function or loop, alongside
/// metadata indicating their origin.
#[derive(Deref, PartialEq, Eq, Hash, Clone, Debug)]
pub struct PcgCoupledEdges<'tcx>(
    FunctionCallOrLoop<FunctionCoupledEdges<'tcx>, LoopCoupledEdges<'tcx>>,
);

impl<'tcx> PcgCoupledEdges<'tcx> {
    pub(crate) fn conditions(&self) -> &ValidityConditions {
        match &self.0 {
            FunctionCallOrLoop::FunctionCall(function) => &function.metadata.conditions,
            FunctionCallOrLoop::Loop(loop_) => &loop_.metadata.conditions,
        }
    }
    pub(crate) fn function_call(edges: FunctionCoupledEdges<'tcx>) -> Self {
        Self(FunctionCallOrLoop::FunctionCall(edges))
    }
    pub(crate) fn loop_(edges: LoopCoupledEdges<'tcx>) -> Self {
        Self(FunctionCallOrLoop::Loop(edges))
    }
    pub(crate) fn edges(&self) -> HashSet<PcgCoupledEdgeKind<'tcx>> {
        fn for_function_call(data: FunctionCoupledEdges<'_>) -> HashSet<PcgCoupledEdgeKind<'_>> {
            data.edges
                .0
                .into_iter()
                .map(|edge| {
                    PcgCoupledEdgeKind::function_call(FunctionCallCoupledEdgeKind::new(
                        data.metadata.value,
                        edge,
                    ))
                })
                .collect()
        }
        fn for_loop(data: LoopCoupledEdges<'_>) -> HashSet<PcgCoupledEdgeKind<'_>> {
            data.edges
                .0
                .into_iter()
                .map(|edge| {
                    PcgCoupledEdgeKind::loop_(LoopCoupledEdgeKind::new(data.metadata.value, edge))
                })
                .collect()
        }
        self.0.clone().bimap(for_function_call, for_loop)
    }
}

/// A collection of hyper edges generated for a function or loop, alongside
/// metadata indicating their origin.
#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub struct CoupledEdges<Metadata, InputNode, OutputNode> {
    pub(crate) metadata: Metadata,
    pub(crate) edges: CoupledEdgesData<InputNode, OutputNode>,
}

type FunctionCoupledEdges<'tcx> = CoupledEdges<
    Conditioned<FunctionCallAbstractionEdgeMetadata<'tcx>>,
    FunctionCallAbstractionInput<'tcx>,
    FunctionCallAbstractionOutput<'tcx>,
>;

type LoopCoupledEdges<'tcx> = CoupledEdges<
    Conditioned<LoopAbstractionEdgeMetadata>,
    LoopAbstractionInput<'tcx>,
    LoopAbstractionOutput<'tcx>,
>;

/// A collection of hyper edges generated for a function or loop, without
/// identifying metadata.
#[derive(Eq, Hash, PartialEq, Clone, Debug, Deref, IntoIterator)]
pub struct CoupledEdgesData<InputNode, OutputNode>(
    pub(crate) Vec<HyperEdge<InputNode, OutputNode>>,
);

impl<InputNode: Eq + Hash, OutputNode: Eq + Hash> CoupledEdgesData<InputNode, OutputNode> {
    #[must_use]
    pub fn into_hash_set(self) -> HashSet<HyperEdge<InputNode, OutputNode>> {
        self.0.into_iter().collect()
    }
}

impl<'tcx, Ctxt: Copy + DebugCtxt, P: PcgPlace<'tcx, Ctxt>> LabelEdgePlaces<'tcx, Ctxt, P>
    for PcgCoupledEdgeKind<'tcx, P>
where
    FunctionCallCoupledEdgeKind<'tcx, P>: LabelEdgePlaces<'tcx, Ctxt, P>,
    LoopCoupledEdgeKind<'tcx, P>: LabelEdgePlaces<'tcx, Ctxt, P>,
{
    fn label_blocked_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>> {
        match &mut self.0 {
            FunctionCallOrLoop::FunctionCall(function) => {
                function.label_blocked_places(predicate, labeller, ctxt)
            }
            FunctionCallOrLoop::Loop(loop_) => {
                loop_.label_blocked_places(predicate, labeller, ctxt)
            }
        }
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>> {
        match &mut self.0 {
            FunctionCallOrLoop::FunctionCall(function) => {
                function.label_blocked_by_places(predicate, labeller, ctxt)
            }
            FunctionCallOrLoop::Loop(loop_) => {
                loop_.label_blocked_by_places(predicate, labeller, ctxt)
            }
        }
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for PcgCoupledEdgeKind<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        match self {
            PcgCoupledEdgeKind(FunctionCallOrLoop::FunctionCall(function)) => {
                function.display_output(ctxt, mode)
            }
            PcgCoupledEdgeKind(FunctionCallOrLoop::Loop(loop_)) => loop_.display_output(ctxt, mode),
        }
    }
}

impl<'tcx, P: PcgNodeComponent> PcgCoupledEdgeKind<'tcx, P> {
    pub(crate) fn function_call(edge: FunctionCallCoupledEdgeKind<'tcx, P>) -> Self {
        Self(FunctionCallOrLoop::FunctionCall(edge))
    }
    pub(crate) fn loop_(edge: LoopCoupledEdgeKind<'tcx, P>) -> Self {
        Self(FunctionCallOrLoop::Loop(edge))
    }
    pub fn inputs<Ctxt>(&self, ctxt: Ctxt) -> Vec<AbstractionInputTarget<'tcx, P>>
    where
        P: PcgPlace<'tcx, Ctxt>,
    {
        match &self.0 {
            FunctionCallOrLoop::FunctionCall(function) => function
                .inputs()
                .iter()
                .map(|input| AbstractionInputTarget((*input).to_pcg_node(ctxt)))
                .collect(),
            FunctionCallOrLoop::Loop(loop_) => loop_
                .inputs()
                .iter()
                .map(|input| AbstractionInputTarget((*input).to_pcg_node(ctxt)))
                .collect(),
        }
    }

    #[must_use]
    pub fn outputs(&self) -> Vec<AbstractionOutputTarget<'tcx, P>> {
        match &self.0 {
            FunctionCallOrLoop::FunctionCall(function) => function
                .outputs()
                .iter()
                .map(|output| AbstractionOutputTarget(PcgNode::LifetimeProjection(output.rebase())))
                .collect(),
            FunctionCallOrLoop::Loop(loop_) => loop_
                .outputs()
                .iter()
                .map(|output| AbstractionOutputTarget(**output))
                .collect(),
        }
    }
}

impl<
    'a,
    'tcx,
    Metadata,
    Ctxt: Copy + DebugCtxt + HasCompilerCtxt<'a, 'tcx>,
    P: PcgPlace<'tcx, Ctxt>,
    Input: LabelPlace<'tcx, Ctxt, P> + PcgNodeLike<'tcx, Ctxt, P>,
    Output: LabelPlace<'tcx, Ctxt, P> + PcgNodeLike<'tcx, Ctxt, P>,
> LabelEdgePlaces<'tcx, Ctxt, P> for CoupledEdgeKind<Metadata, Input, Output>
{
    fn label_blocked_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>> {
        self.edge.label_blocked_places(predicate, labeller, ctxt)
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>> {
        self.edge.label_blocked_by_places(predicate, labeller, ctxt)
    }
}
