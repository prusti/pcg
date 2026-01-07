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
        edge_data::{EdgeData, LabelEdgePlaces, LabelNodePredicate, NodeReplacement},
        has_pcs_elem::{LabelLifetimeProjection, LabelLifetimeProjectionResult, PlaceLabeller},
        region_projection::LifetimeProjectionLabel,
        validity_conditions::ValidityConditions,
    },
    pcg::PcgNode,
    rustc_interface::middle::mir::{self, BasicBlock, Location},
    utils::display::{DisplayOutput, OutputMode},
    utils::{
        CompilerCtxt, data_structures::HashSet, display::DisplayWithCtxt,
        validity::HasValidityCheck,
    },
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
    fn display_output(&self, _ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(format!("Loop({:?})", self.0).into())
    }
}

pub type LoopAbstraction<'tcx> =
    AbstractionBlockEdgeWithMetadata<LoopAbstractionEdgeMetadata, LoopAbstractionEdge<'tcx>>;

impl<'a, 'tcx> LabelLifetimeProjection<'a, 'tcx> for LoopAbstraction<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        projection: &LabelNodePredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        self.edge.label_lifetime_projection(projection, label, ctxt)
    }
}
impl<'tcx> EdgeData<'tcx> for LoopAbstraction<'tcx> {
    fn blocks_node<'slf>(&self, node: BlockedNode<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.edge.blocks_node(node, ctxt)
    }
    fn blocked_nodes<'slf, BC: Copy>(
        &'slf self,
        ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = PcgNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        self.edge.blocked_nodes(ctxt)
    }

    fn blocked_by_nodes<'slf, 'mir: 'slf, BC: Copy + 'slf>(
        &'slf self,
        ctxt: CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        self.edge.blocked_by_nodes(ctxt)
    }
}

impl<'tcx> LabelEdgePlaces<'tcx> for LoopAbstraction<'tcx> {
    fn label_blocked_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> HashSet<NodeReplacement<'tcx>> {
        self.edge.label_blocked_places(predicate, labeller, ctxt)
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> HashSet<NodeReplacement<'tcx>> {
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
