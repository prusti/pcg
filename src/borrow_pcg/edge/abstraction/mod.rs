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
        edge_data::{LabelEdgePlaces, LabelPlacePredicate, edgedata_enum},
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionPredicate,
            LabelLifetimeProjectionResult, LabelNodeContext, LabelPlaceWithContext, PlaceLabeller,
        },
        region_projection::{LifetimeProjectionLabel, PcgLifetimeProjectionBase},
    },
    pcg::PCGNodeLike,
    utils::{HasBorrowCheckerCtxt, maybe_remote::MaybeRemotePlace},
};

use crate::borrow_pcg::borrow_pcg_edge::LocalNode;
use crate::borrow_pcg::domain::LoopAbstractionInput;
use crate::borrow_pcg::edge_data::EdgeData;
use crate::borrow_pcg::region_projection::LifetimeProjection;
use crate::pcg::PcgNode;
use crate::utils::CompilerCtxt;
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::validity::HasValidityCheck;

/// Either a function call or a loop abstraction
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum AbstractionType<'tcx> {
    FunctionCall(FunctionCallAbstraction<'tcx>),
    Loop(LoopAbstraction<'tcx>),
}

edgedata_enum!(
    AbstractionType<'tcx>,
    FunctionCall(FunctionCallAbstraction<'tcx>),
    Loop(LoopAbstraction<'tcx>),
);

/// A hyperedge for a function or loop abstraction
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct AbstractionBlockEdge<'tcx, Input, Output> {
    _phantom: PhantomData<&'tcx ()>,
    input: Input,
    pub(crate) output: Output,
}

impl<
    'tcx,
    T: LabelPlaceWithContext<'tcx, LabelNodeContext>,
    U: LabelPlaceWithContext<'tcx, LabelNodeContext>,
> LabelEdgePlaces<'tcx> for AbstractionBlockEdge<'tcx, T, U>
{
    fn label_blocked_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.input
            .label_place_with_context(predicate, labeller, LabelNodeContext::Other, ctxt)
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.output
            .label_place_with_context(predicate, labeller, LabelNodeContext::Other, ctxt)
    }
}

impl<
    'tcx: 'a,
    'a,
    Input: LabelLifetimeProjection<'tcx>
        + PCGNodeLike<'tcx>
        + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    Output: LabelLifetimeProjection<'tcx>
        + PCGNodeLike<'tcx>
        + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
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
        self.assert_validity(ctxt);
        changed |= self
            .output
            .label_lifetime_projection(projection, label, ctxt);
        self.assert_validity(ctxt);
        changed
    }
}

trait AbstractionInputLike<'tcx>: Sized + Clone + Copy {
    fn blocks<C: Copy>(&self, node: BlockedNode<'tcx>, ctxt: CompilerCtxt<'_, 'tcx, C>) -> bool;

    fn to_abstraction_input(self) -> AbstractionInputTarget<'tcx>;
}

impl<'tcx> AbstractionInputLike<'tcx> for LoopAbstractionInput<'tcx> {
    fn blocks<C: Copy>(&self, node: BlockedNode<'tcx>, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> bool {
        match node {
            PcgNode::Place(p) => *self == p.into(),
            PcgNode::LifetimeProjection(region_projection) => match region_projection.base {
                PcgLifetimeProjectionBase::Place(maybe_remote_place) => {
                    *self == (region_projection.with_base(maybe_remote_place).into())
                }
                PcgLifetimeProjectionBase::Const(_) => false,
            },
        }
    }

    fn to_abstraction_input(self) -> AbstractionInputTarget<'tcx> {
        AbstractionInputTarget(self.0)
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, MaybeRemotePlace<'tcx>>> for LoopAbstractionInput<'tcx> {
    fn from(value: LifetimeProjection<'tcx, MaybeRemotePlace<'tcx>>) -> Self {
        LoopAbstractionInput(PcgNode::LifetimeProjection(value.into()))
    }
}

impl<'tcx> AbstractionInputLike<'tcx> for FunctionCallAbstractionInput<'tcx> {
    fn blocks<C: Copy>(&self, node: BlockedNode<'tcx>, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> bool {
        match node {
            PcgNode::Place(_) => false,
            PcgNode::LifetimeProjection(region_projection) => match region_projection.base {
                PcgLifetimeProjectionBase::Place(MaybeRemotePlace::Local(rp)) => {
                    *self == region_projection.with_base(rp).into()
                }
                _ => false,
            },
        }
    }

    fn to_abstraction_input(self) -> AbstractionInputTarget<'tcx> {
        AbstractionInputTarget(self.0.into())
    }
}

impl<'tcx, Input: AbstractionInputLike<'tcx>, Output: Copy + PCGNodeLike<'tcx>> EdgeData<'tcx>
    for AbstractionBlockEdge<'tcx, Input, Output>
{
    fn blocks_node<'slf>(&self, node: BlockedNode<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.input.blocks(node, ctxt)
    }

    fn blocked_nodes<'slf, BC: Copy>(
        &'slf self,
        ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = PcgNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(std::iter::once(
            self.input.to_abstraction_input().to_pcg_node(ctxt),
        ))
    }

    fn blocked_by_nodes<'slf, 'mir, BC: Copy + 'slf>(
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

impl<
    'tcx,
    'a,
    Input: DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    Output: DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for AbstractionBlockEdge<'tcx, Input, Output>
{
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
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
    Input: HasValidityCheck<'tcx>
        + PCGNodeLike<'tcx>
        + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    Output: HasValidityCheck<'tcx>
        + PCGNodeLike<'tcx>
        + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
> HasValidityCheck<'tcx> for AbstractionBlockEdge<'tcx, Input, Output>
{
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
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
    Input: Clone + PCGNodeLike<'tcx> + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    Output: Clone + PCGNodeLike<'tcx> + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
> AbstractionBlockEdge<'tcx, Input, Output>
{
    pub(crate) fn new(
        input: Input,
        output: Output,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Self {
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
