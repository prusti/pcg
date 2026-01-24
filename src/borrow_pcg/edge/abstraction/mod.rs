//! Function and loop abstractions
pub(crate) mod function;
pub(crate) mod r#loop;
pub(crate) mod r#type;

use std::marker::PhantomData;

use crate::borrow_pcg::edge_data::conditionally_label_places;
use crate::utils::{DebugCtxt, PcgPlace, Place};
use crate::{
    borrow_pcg::{
        borrow_pcg_edge::BlockedNode,
        domain::{AbstractionInputTarget, FunctionCallAbstractionInput},
        edge::{
            abstraction::{function::FunctionCallAbstraction, r#loop::LoopAbstraction},
            kind::BorrowPcgEdgeType,
        },
        edge_data::{
            LabelEdgeLifetimeProjections, LabelEdgePlaces, LabelNodePredicate, NodeReplacement,
            edgedata_enum,
        },
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionResult, LabelNodeContext, LabelPlace,
            PlaceLabeller, SourceOrTarget,
        },
        region_projection::{LifetimeProjectionLabel, PlaceOrConst},
    },
    coupling::HyperEdge,
    pcg::PcgNodeLike,
    utils::{
        data_structures::HashSet,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        maybe_remote::MaybeRemotePlace,
    },
};

use crate::coupling::PcgCoupledEdgeKind;

use crate::{
    borrow_pcg::{
        borrow_pcg_edge::LocalNode, domain::LoopAbstractionInput, edge_data::EdgeData,
        region_projection::LifetimeProjection,
    },
    pcg::PcgNode,
    utils::validity::HasValidityCheck,
};

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum FunctionCallOrLoop<FunctionCallData, LoopData> {
    FunctionCall(FunctionCallData),
    Loop(LoopData),
}

impl<FunctionCallData, LoopData> FunctionCallOrLoop<FunctionCallData, LoopData> {
    pub(crate) fn bimap<R>(
        self,
        f: impl FnOnce(FunctionCallData) -> R,
        g: impl FnOnce(LoopData) -> R,
    ) -> R {
        match self {
            FunctionCallOrLoop::FunctionCall(data) => f(data),
            FunctionCallOrLoop::Loop(data) => g(data),
        }
    }
}

edgedata_enum!(
    crate::borrow_pcg::edge::abstraction::AbstractionEdge,
    AbstractionEdge<'tcx, P>,
    FunctionCall(super::function::FunctionCallAbstraction<'tcx, P>),
    Loop(super::r#loop::LoopAbstraction<'tcx, P>),
);

pub type AbstractionEdge<'tcx, P = Place<'tcx>> =
    FunctionCallOrLoop<FunctionCallAbstraction<'tcx, P>, LoopAbstraction<'tcx, P>>;

impl<'tcx> AbstractionEdge<'tcx> {
    /// Creates a singleton coupling hyperedge from this edge.
    ///
    /// This is presumably NOT what you want, as there is no coupling logic
    /// involved.  Instead, consider [`BorrowsGraph::coupling_results`].
    /// However, Prusti is currently using this function for loops.
    pub fn into_singleton_coupled_edge(self) -> PcgCoupledEdgeKind<'tcx> {
        match self {
            AbstractionEdge::FunctionCall(function_call) => {
                PcgCoupledEdgeKind::function_call(function_call.into_singleton_coupled_edge())
            }
            AbstractionEdge::Loop(loop_abstraction) => {
                PcgCoupledEdgeKind::loop_(loop_abstraction.into_singleton_coupled_edge())
            }
        }
    }
}

impl<'tcx, Input: std::fmt::Display, Output: std::fmt::Display> std::fmt::Display
    for AbstractionBlockEdge<'tcx, Input, Output>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} -> {}", self.input, self.output)
    }
}

/// An edge for a function or loop abstraction
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct AbstractionBlockEdge<'tcx, Input, Output> {
    _phantom: PhantomData<&'tcx ()>,
    pub(crate) input: Input,
    pub(crate) output: Output,
}

impl<'tcx, Input: Copy, Output: Copy> AbstractionBlockEdge<'tcx, Input, Output> {
    pub(crate) fn new(input: Input, output: Output) -> Self {
        Self {
            _phantom: PhantomData,
            input,
            output,
        }
    }

    pub(crate) fn to_singleton_hyper_edge(self) -> HyperEdge<Input, Output> {
        HyperEdge::new(vec![self.input], vec![self.output])
    }
}

impl<
    'tcx,
    Ctxt: DebugCtxt + Copy,
    P: PcgPlace<'tcx, Ctxt>,
    T: LabelPlace<'tcx, Ctxt, P> + PcgNodeLike<'tcx, Ctxt, P>,
    U: LabelPlace<'tcx, Ctxt, P> + PcgNodeLike<'tcx, Ctxt, P>,
> LabelEdgePlaces<'tcx, Ctxt, P> for AbstractionBlockEdge<'tcx, T, U>
{
    fn label_blocked_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>> {
        conditionally_label_places(
            vec![&mut self.input],
            predicate,
            labeller,
            LabelNodeContext::new(SourceOrTarget::Source, BorrowPcgEdgeType::Abstraction),
            ctxt,
        )
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>> {
        conditionally_label_places(
            vec![&mut self.output],
            predicate,
            labeller,
            LabelNodeContext::new(SourceOrTarget::Target, BorrowPcgEdgeType::Abstraction),
            ctxt,
        )
    }
}

impl<
    'tcx,
    Ctxt: Copy,
    P: PcgPlace<'tcx, Ctxt>,
    Input: LabelLifetimeProjection<'tcx> + PcgNodeLike<'tcx, Ctxt, P>,
    Output: LabelLifetimeProjection<'tcx> + PcgNodeLike<'tcx, Ctxt, P>,
> LabelEdgeLifetimeProjections<'tcx, Ctxt, P> for AbstractionBlockEdge<'tcx, Input, Output>
{
    fn label_lifetime_projections(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: Ctxt,
    ) -> LabelLifetimeProjectionResult {
        let source_context =
            LabelNodeContext::new(SourceOrTarget::Source, BorrowPcgEdgeType::Abstraction);
        let target_context =
            LabelNodeContext::new(SourceOrTarget::Target, BorrowPcgEdgeType::Abstraction);
        let mut changed = LabelLifetimeProjectionResult::Unchanged;
        if predicate.applies_to(self.input.to_pcg_node(ctxt), source_context) {
            changed |= self.input.label_lifetime_projection(label);
        }
        if predicate.applies_to(self.output.to_pcg_node(ctxt), target_context) {
            changed |= self.output.label_lifetime_projection(label);
        }
        changed
    }
}

trait AbstractionInputLike<'tcx, Ctxt, P>: Sized + Clone + Copy {
    fn blocks(&self, node: BlockedNode<'tcx, P>, ctxt: Ctxt) -> bool;

    fn to_abstraction_input(self, ctxt: Ctxt) -> AbstractionInputTarget<'tcx, P>;
}

impl<'tcx, Ctxt, P: PcgPlace<'tcx, Ctxt>> AbstractionInputLike<'tcx, Ctxt, P>
    for LoopAbstractionInput<'tcx, P>
{
    fn blocks(&self, node: BlockedNode<'tcx, P>, _ctxt: Ctxt) -> bool {
        match node {
            PcgNode::Place(p) => **self == p.into(),
            PcgNode::LifetimeProjection(region_projection) => match region_projection.base {
                PlaceOrConst::Place(_) => **self == PcgNode::LifetimeProjection(region_projection),
                PlaceOrConst::Const(_) => false,
            },
        }
    }

    fn to_abstraction_input(self, _ctxt: Ctxt) -> AbstractionInputTarget<'tcx, P> {
        AbstractionInputTarget(self.0)
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, MaybeRemotePlace<'tcx>>> for LoopAbstractionInput<'tcx> {
    fn from(value: LifetimeProjection<'tcx, MaybeRemotePlace<'tcx>>) -> Self {
        LoopAbstractionInput(PcgNode::LifetimeProjection(value.into()))
    }
}

impl<'tcx, Ctxt, P: PcgPlace<'tcx, Ctxt>> AbstractionInputLike<'tcx, Ctxt, P>
    for FunctionCallAbstractionInput<'tcx, P>
{
    fn blocks(&self, node: BlockedNode<'tcx, P>, ctxt: Ctxt) -> bool {
        self.to_pcg_node(ctxt) == node
    }

    fn to_abstraction_input(self, ctxt: Ctxt) -> AbstractionInputTarget<'tcx, P> {
        AbstractionInputTarget(self.to_pcg_node(ctxt))
    }
}

impl<
    'tcx,
    Ctxt,
    P: PcgPlace<'tcx, Ctxt>,
    Input: AbstractionInputLike<'tcx, Ctxt, P>,
    Output: Copy + PcgNodeLike<'tcx, Ctxt, P>,
> EdgeData<'tcx, Ctxt, P> for AbstractionBlockEdge<'tcx, Input, Output>
{
    fn blocks_node<'slf>(&self, node: BlockedNode<'tcx, P>, ctxt: Ctxt) -> bool {
        self.input.blocks(node, ctxt)
    }

    fn blocked_nodes<'slf>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Box<dyn std::iter::Iterator<Item = BlockedNode<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(std::iter::once(
            self.input.to_abstraction_input(ctxt).to_pcg_node(ctxt),
        ))
    }

    fn blocked_by_nodes<'slf>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(std::iter::once(
            self.output
                .to_pcg_node(ctxt)
                .try_to_local_node(ctxt)
                .unwrap(),
        ))
    }
}

impl<'tcx, Ctxt: Copy, Input: DisplayWithCtxt<Ctxt>, Output: DisplayWithCtxt<Ctxt>>
    DisplayWithCtxt<Ctxt> for AbstractionBlockEdge<'tcx, Input, Output>
{
    fn display_output(&self, ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(
            format!(
                "{} -> {}",
                self.input.display_string(ctxt),
                self.output.display_string(ctxt),
            )
            .into(),
        )
    }
}

impl<
    'tcx,
    Ctxt: DebugCtxt + Copy,
    Input: HasValidityCheck<Ctxt> + DisplayWithCtxt<Ctxt>,
    Output: HasValidityCheck<Ctxt> + DisplayWithCtxt<Ctxt>,
> HasValidityCheck<Ctxt> for AbstractionBlockEdge<'tcx, Input, Output>
{
    fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
        self.input.check_validity(ctxt)?;
        self.output.check_validity(ctxt)?;
        // if self.input.to_pcg_node(ctxt) == self.output.to_pcg_node(ctxt) {
        //     return Err(format!(
        //         "Input {:?} and output {:?} are the same node",
        //         self.input, self.output,
        //     ));
        // }
        Ok(())
    }
}

impl<'tcx, Input, Output> AbstractionBlockEdge<'tcx, Input, Output> {
    pub(crate) fn new_checked<Ctxt: DebugCtxt + Copy>(
        input: Input,
        output: Output,
        ctxt: Ctxt,
    ) -> Self
    where
        Self: HasValidityCheck<Ctxt>,
    {
        let result = Self {
            _phantom: PhantomData,
            input,
            output,
        };
        result.assert_validity(ctxt);
        result
    }
}

impl<Input: Clone, Output: Copy> AbstractionBlockEdge<'_, Input, Output> {
    pub fn output(&self) -> Output {
        self.output
    }

    pub fn input(&self) -> Input {
        self.input.clone()
    }
}
