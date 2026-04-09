use crate::{
    borrow_pcg::edge::kind::BorrowPcgEdgeKind, error::PcgError, pcg::{
        PcgRefLike, obtain::ObtainType, triple::{PlaceCondition, Triple}
    }, utils::{DataflowCtxt, Place}
};

use super::PcgVisitor;

impl<'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PcgVisitor<'_, 'a, 'tcx, Ctxt> {
    #[tracing::instrument(skip(self))]
    pub(crate) fn require_triple(&mut self, triple: Triple<'tcx>) -> Result<(), PcgError<'tcx>> {
        match triple.pre() {
            PlaceCondition::ExpandTwoPhase(place) => {
                    self.place_obtainer()
                        .obtain(place, ObtainType::TwoPhaseExpand)?;
            }
            PlaceCondition::Capability(place, capability) => {
                    self.place_obtainer()
                        .obtain(place, ObtainType::Capability(capability))?;
            }
            PlaceCondition::AllocateOrDeallocate(local) => {
                if self.pcg.owned[local].is_unallocated() {
                    // Could happen if there is a storagedead for an already conditionally dead local
                    return Ok(());
                }
                self.place_obtainer()
                    .obtain(local.into(), ObtainType::ForStorageDead)?;

                // With raw pointers, we can have dangling pointers
                // Remove any incoming delegation edges
                let place: Place = local.into();
                let blocking_edges = self.pcg.borrows_graph().edges_blocking(place.into(), self.ctxt.bc_ctxt());
                
                let mut to_remove = vec![];
                for edge in blocking_edges {
                    match edge.kind {
                        BorrowPcgEdgeKind::Delegation(_) => {to_remove.push(edge.kind().clone())}
                        _ => {}
                    }
                };

                for edge in to_remove {
                    self.pcg.borrow.graph.remove(&edge);
                }
            }
            PlaceCondition::Unalloc(_) | PlaceCondition::Return => {}
            PlaceCondition::RemoveCapability(_) => unreachable!(),
        }
        Ok(())
    }

    #[tracing::instrument(skip(self, triple))]
    pub(crate) fn ensure_triple(&mut self, triple: Triple<'tcx>) -> Result<(), PcgError<'tcx>> {
        self.pcg.ensure_triple(triple, self.ctxt);
        Ok(())
    }
}
