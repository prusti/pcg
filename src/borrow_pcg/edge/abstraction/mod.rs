//! Function and loop abstractions
pub(crate) mod function;
pub(crate) mod r#loop;
pub(crate) mod r#type;

use std::marker::PhantomData;

use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        borrow_pcg_edge::BlockedNode,
        domain::{AbstractionInputTarget, FunctionCallAbstractionInput},
        edge::abstraction::{function::FunctionCallAbstraction, r#loop::LoopAbstraction},
        edge_data::{edgedata_enum, LabelEdgePlaces, LabelPlacePredicate},
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionPredicate,
            LabelLifetimeProjectionResult, LabelNodeContext, LabelPlaceWithContext, PlaceLabeller,
        },
        region_projection::{LifetimeProjectionLabel, PlaceOrConst},
    },
    coupling::HyperEdge,
    pcg::PcgNodeLike,
    utils::{maybe_remote::MaybeRemotePlace, CtxtExtra, HasBorrowCheckerCtxt, HasCompilerCtxt},
};

use crate::coupling::PcgCoupledEdgeKind;

use crate::{
    borrow_pcg::{
        borrow_pcg_edge::LocalNode, domain::LoopAbstractionInput, edge_data::EdgeData,
        region_projection::LifetimeProjection,
    },
    pcg::PcgNode,
    utils::{CompilerCtxt, display::DisplayWithCompilerCtxt, validity::HasValidityCheck},
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

pub type AbstractionEdge<'tcx> =
    FunctionCallOrLoop<FunctionCallAbstraction<'tcx>, LoopAbstraction<'tcx>>;

edgedata_enum!(
    AbstractionEdge<'tcx>,
    FunctionCall(FunctionCallAbstraction<'tcx>),
    Loop(LoopAbstraction<'tcx>),
);

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
    T: LabelPlaceWithContext<'tcx, LabelNodeContext>,
    U: LabelPlaceWithContext<'tcx, LabelNodeContext>,
> LabelEdgePlaces<'tcx> for AbstractionBlockEdge<'tcx, T, U>
{
    fn label_blocked_places<'a>(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        self.input
            .label_place_with_context(predicate, labeller, LabelNodeContext::Other, ctxt)
    }

    fn label_blocked_by_places<'a>(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        self.output
            .label_place_with_context(predicate, labeller, LabelNodeContext::Other, ctxt)
    }
}

impl<
    'tcx: 'a,
    'a,
    Input: LabelLifetimeProjection<'tcx> + PcgNodeLike<'tcx> + DisplayWithCompilerCtxt<'a, 'tcx>,
    Output: LabelLifetimeProjection<'tcx> + PcgNodeLike<'tcx> + DisplayWithCompilerCtxt<'a, 'tcx>,
> LabelLifetimeProjection<'tcx> for AbstractionBlockEdge<'tcx, Input, Output>
{
    fn label_lifetime_projection(
        &mut self,
        projection: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        let mut changed = LabelLifetimeProjectionResult::Unchanged;
        changed |= self
            .input
            .label_lifetime_projection(projection, label, ctxt);
        changed |= self
            .output
            .label_lifetime_projection(projection, label, ctxt);
        changed
    }
}

trait AbstractionInputLike<'tcx>: Sized + Clone + Copy {
    fn blocks<C: crate::utils::CtxtExtra>(
        &self,
        node: BlockedNode<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> bool;

    fn to_abstraction_input<C: crate::utils::CtxtExtra>(
        self,
        ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> AbstractionInputTarget<'tcx>;
}

impl<'tcx> AbstractionInputLike<'tcx> for LoopAbstractionInput<'tcx> {
    fn blocks<C: crate::utils::CtxtExtra>(
        &self,
        node: BlockedNode<'tcx>,
        _ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> bool {
        match node {
            PcgNode::Place(p) => *self == p.into(),
            PcgNode::LifetimeProjection(region_projection) => match region_projection.base {
                PlaceOrConst::Place(maybe_remote_place) => {
                    *self == (region_projection.with_base(maybe_remote_place).into())
                }
                PlaceOrConst::Const(_) => false,
            },
        }
    }

    fn to_abstraction_input<C: crate::utils::CtxtExtra>(
        self,
        _ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> AbstractionInputTarget<'tcx> {
        AbstractionInputTarget(self.0)
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, MaybeRemotePlace<'tcx>>> for LoopAbstractionInput<'tcx> {
    fn from(value: LifetimeProjection<'tcx, MaybeRemotePlace<'tcx>>) -> Self {
        LoopAbstractionInput(PcgNode::LifetimeProjection(value.into()))
    }
}

impl<'tcx> AbstractionInputLike<'tcx> for FunctionCallAbstractionInput<'tcx> {
    fn blocks<C: crate::utils::CtxtExtra>(
        &self,
        node: BlockedNode<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> bool {
        self.to_pcg_node(ctxt) == node
    }

    fn to_abstraction_input<C: crate::utils::CtxtExtra>(
        self,
        ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> AbstractionInputTarget<'tcx> {
        AbstractionInputTarget(self.to_pcg_node(ctxt))
    }
}

impl<'tcx, Input: AbstractionInputLike<'tcx>, Output: Copy + PcgNodeLike<'tcx>> EdgeData<'tcx>
    for AbstractionBlockEdge<'tcx, Input, Output>
{
    fn blocks_node<'slf>(&self, node: BlockedNode<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.input.blocks(node, ctxt)
    }

    fn blocked_nodes<'slf, BC: crate::utils::CtxtExtra>(
        &'slf self,
        ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = PcgNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(std::iter::once(
            self.input.to_abstraction_input(ctxt).to_pcg_node(ctxt),
        ))
    }

    fn blocked_by_nodes<'slf, 'mir, BC: crate::utils::CtxtExtra + 'slf>(
        &'slf self,
        ctxt: CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx>> + 'slf>
    where
        'tcx: 'mir,
        'mir: 'slf,
    {
        Box::new(std::iter::once(
            self.output
                .to_pcg_node(ctxt)
                .try_to_local_node(ctxt)
                .unwrap(),
        ))
    }
}

impl<'tcx, 'a, Input: DisplayWithCompilerCtxt<'a, 'tcx>, Output: DisplayWithCompilerCtxt<'a, 'tcx>>
    DisplayWithCompilerCtxt<'a, 'tcx> for AbstractionBlockEdge<'tcx, Input, Output>
{
    fn to_short_string(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> String {
        format!(
            "{} -> {}",
            self.input.to_short_string(ctxt),
            self.output.to_short_string(ctxt),
        )
    }
}

impl<
    'tcx: 'a,
    'a,
    Input: HasValidityCheck<'a, 'tcx> + PcgNodeLike<'tcx> + DisplayWithCompilerCtxt<'a, 'tcx>,
    Output: HasValidityCheck<'a, 'tcx> + PcgNodeLike<'tcx> + DisplayWithCompilerCtxt<'a, 'tcx>,
> HasValidityCheck<'a, 'tcx> for AbstractionBlockEdge<'tcx, Input, Output>
{
    fn check_validity(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> Result<(), String> {
        self.input.check_validity(ctxt)?;
        self.output.check_validity(ctxt)?;
        if self.input.to_pcg_node(ctxt) == self.output.to_pcg_node(ctxt) {
            return Err(format!(
                "Input {:?} and output {:?} are the same node",
                self.input, self.output,
            ));
        }
        Ok(())
    }
}

impl<
    'tcx: 'a,
    'a,
    Input: Clone + PcgNodeLike<'tcx> + DisplayWithCompilerCtxt<'a, 'tcx>,
    Output: Clone + PcgNodeLike<'tcx> + DisplayWithCompilerCtxt<'a, 'tcx>,
> AbstractionBlockEdge<'tcx, Input, Output>
{
    pub(crate) fn new_checked(
        input: Input,
        output: Output,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Self
    where
        Self: HasValidityCheck<'a, 'tcx>,
    {
        let result = Self {
            _phantom: PhantomData,
            input,
            output,
        };
        result.assert_validity(ctxt.bc_ctxt());
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
