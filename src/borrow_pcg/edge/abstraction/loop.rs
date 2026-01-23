use derive_more::From;

use super::AbstractionBlockEdge;
use crate::{
    borrow_pcg::{
        borrow_pcg_edge::{BlockedNode, BorrowPcgEdge, LocalNode},
        domain::LoopAbstractionOutput,
        edge::{
            abstraction::{
                AbstractionEdge, LoopAbstractionInput, function::AbstractionBlockEdgeWithMetadata,
            },
            kind::BorrowPcgEdgeKind,
        },
        edge_data::{
            EdgeData, LabelEdgeLifetimeProjections, LabelEdgePlaces, LabelNodePredicate,
            NodeReplacement, label_edge_lifetime_projections_wrapper, label_edge_places_wrapper,
        },
        has_pcs_elem::{LabelLifetimeProjectionResult, PlaceLabeller},
        region_projection::LifetimeProjectionLabel,
        validity_conditions::ValidityConditions,
    },
    pcg::PcgNode,
    rustc_interface::middle::mir::{self, BasicBlock, Location},
    utils::{
        CompilerCtxt, DebugCtxt, Place,
        data_structures::HashSet,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        validity::{HasValidityCheck, has_validity_check_node_wrapper},
    },
};

pub(crate) type LoopAbstractionEdge<'tcx, P = Place<'tcx>> =
    AbstractionBlockEdge<'tcx, LoopAbstractionInput<'tcx, P>, LoopAbstractionOutput<'tcx>>;

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

pub type LoopAbstraction<'tcx, P = Place<'tcx>> =
    AbstractionBlockEdgeWithMetadata<LoopAbstractionEdgeMetadata, LoopAbstractionEdge<'tcx, P>>;

label_edge_places_wrapper!(LoopAbstraction<'tcx, P>);
label_edge_lifetime_projections_wrapper!(LoopAbstraction<'tcx, P>);

impl<'a, 'tcx: 'a> EdgeData<'tcx, CompilerCtxt<'a, 'tcx>> for LoopAbstraction<'tcx> {
    fn blocks_node<'slf>(&self, node: BlockedNode<'tcx>, ctxt: CompilerCtxt<'a, 'tcx>) -> bool {
        self.edge.blocks_node(node, ctxt)
    }
    fn blocked_nodes<'slf>(
        &'slf self,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> Box<dyn std::iter::Iterator<Item = PcgNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        self.edge.blocked_nodes(ctxt)
    }

    fn blocked_by_nodes<'slf>(
        &'slf self,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        self.edge.blocked_by_nodes(ctxt)
    }
}

has_validity_check_node_wrapper!(LoopAbstraction<'tcx, P>);

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
