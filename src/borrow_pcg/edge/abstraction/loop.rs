use derive_more::From;

use super::AbstractionBlockEdge;
use crate::{
    borrow_pcg::{
        borrow_pcg_edge::{BlockedNode, BorrowPcgEdge, LocalNode, ToBorrowsEdge},
        domain::LoopAbstractionOutput,
        edge::{
            abstraction::{
                AbstractionEdge, LoopAbstractionInput, function::AbstractionBlockEdgeWithMetadata,
            },
            kind::BorrowPcgEdgeKind,
        },
        edge_data::{EdgeData, LabelEdgePlaces, LabelPlacePredicate},
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionPredicate,
            LabelLifetimeProjectionResult, PlaceLabeller,
        },
        region_projection::LifetimeProjectionLabel,
        validity_conditions::ValidityConditions,
    },
    pcg::PcgNode,
    rustc_interface::middle::mir::{self, BasicBlock, Location},
    utils::display::DisplayOutput,
    utils::{CompilerCtxt, display::DisplayWithCtxt, validity::HasValidityCheck},
};

pub(crate) type LoopAbstractionEdge<'tcx> =
    AbstractionBlockEdge<'tcx, LoopAbstractionInput<'tcx>, LoopAbstractionOutput<'tcx>>;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, From)]
pub struct LoopAbstractionEdgeMetadata(mir::BasicBlock);

impl LoopAbstractionEdgeMetadata {
    pub(crate) fn loop_head_block(self) -> mir::BasicBlock {
        self.0
    }
}

impl<Ctxt> DisplayWithCtxt<Ctxt> for LoopAbstractionEdgeMetadata {
    fn output(&self, _ctxt: Ctxt) -> DisplayOutput {
        DisplayOutput::Text(format!("Loop({:?})", self.0))
    }
}

pub type LoopAbstraction<'tcx> =
    AbstractionBlockEdgeWithMetadata<LoopAbstractionEdgeMetadata, LoopAbstractionEdge<'tcx>>;

impl<'a, 'tcx> LabelLifetimeProjection<'a, 'tcx> for LoopAbstraction<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        projection: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        repacker: CompilerCtxt<'a, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        self.edge
            .label_lifetime_projection(projection, label, repacker)
    }
}
impl<'tcx> EdgeData<'tcx> for LoopAbstraction<'tcx> {
    fn blocks_node<'slf>(&self, node: BlockedNode<'tcx>, repacker: CompilerCtxt<'_, 'tcx>) -> bool {
        self.edge.blocks_node(node, repacker)
    }
    fn blocked_nodes<'slf, BC: Copy>(
        &'slf self,
        repacker: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = PcgNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        self.edge.blocked_nodes(repacker)
    }

    fn blocked_by_nodes<'slf, 'mir: 'slf, BC: Copy + 'slf>(
        &'slf self,
        repacker: CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        self.edge.blocked_by_nodes(repacker)
    }
}

impl<'tcx> LabelEdgePlaces<'tcx> for LoopAbstraction<'tcx> {
    fn label_blocked_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.edge.label_blocked_places(predicate, labeller, ctxt)
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.edge.label_blocked_by_places(predicate, labeller, ctxt)
    }
}
impl<'tcx> HasValidityCheck<'_, 'tcx> for LoopAbstraction<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.edge.check_validity(ctxt)
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for LoopAbstraction<'tcx> {
    fn to_borrow_pcg_edge(self, path_conditions: ValidityConditions) -> BorrowPcgEdge<'tcx> {
        BorrowPcgEdge::new(
            BorrowPcgEdgeKind::Abstraction(AbstractionEdge::Loop(self)),
            path_conditions,
        )
    }
}

impl<'tcx> LoopAbstraction<'tcx> {
    pub(crate) fn new(
        edge: AbstractionBlockEdge<'tcx, LoopAbstractionInput<'tcx>, LoopAbstractionOutput<'tcx>>,
        block: BasicBlock,
    ) -> Self {
        Self {
            edge,
            metadata: block.into(),
        }
    }

    pub(crate) fn location(&self) -> Location {
        Location {
            block: self.metadata.0,
            statement_index: 0,
        }
    }
}
