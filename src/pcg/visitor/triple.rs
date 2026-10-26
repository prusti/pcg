use crate::{
    action::BorrowPcgAction,
    borrow_pcg::edge::kind::BorrowPcgEdgeKind,
    error::PcgError,
    pcg::{
        CapabilityKind, PcgRefLike,
        obtain::ObtainType,
        place_capabilities::PlaceCapabilitiesReader,
        triple::{PlaceCondition, Triple},
    },
    pcg_validity_assert,
    utils::{DataflowCtxt, Place, display::DisplayWithCompilerCtxt},
};

use super::PcgVisitor;

impl<'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PcgVisitor<'_, 'a, 'tcx, Ctxt> {
    #[tracing::instrument(skip(self))]
    pub(crate) fn require_triple(&mut self, triple: Triple<'tcx>) -> Result<(), PcgError> {
        match triple.pre() {
            PlaceCondition::ExpandTwoPhase(place) => {
                // The reservation obtains `place` as a mutable borrow does,
                // unless `place` is only readable because of a live shared
                // borrow of it or of an ancestor.
                let obtain_type = if self.closest_capability(place) == Some(CapabilityKind::Read) {
                    ObtainType::TwoPhaseExpand
                } else {
                    ObtainType::Capability(CapabilityKind::Exclusive)
                };
                self.place_obtainer().obtain(place, obtain_type)?;
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
                let blocking_edges = self
                    .pcg
                    .borrows_graph()
                    .edges_blocking(place.into(), self.ctxt.bc_ctxt());

                let mut to_remove = vec![];
                for edge in blocking_edges {
                    if let BorrowPcgEdgeKind::Delegation(_) = edge.kind {
                        to_remove.push(edge.kind().clone());
                    }
                }

                for edge in to_remove {
                    self.pcg.borrow.graph.remove(&edge);
                }
            }
            PlaceCondition::Unalloc(_) | PlaceCondition::Return => {}
            PlaceCondition::RemoveCapability(_) | PlaceCondition::Freeze(_) => unreachable!(),
        }
        Ok(())
    }

    /// The capability of `place` or, if it has none, of its closest ancestor
    /// that has one.
    fn closest_capability(&self, place: Place<'tcx>) -> Option<CapabilityKind> {
        let mut current = place;
        loop {
            if let Some(cap) = self.pcg.capability_of(current, self.ctxt) {
                return Some(cap);
            }
            current = current.parent_place()?;
        }
    }

    #[tracing::instrument(skip(self, triple))]
    pub(crate) fn ensure_triple(&mut self, triple: Triple<'tcx>) -> Result<(), PcgError> {
        self.pcg.ensure_triple(triple, self.ctxt);
        if let Some(PlaceCondition::Freeze(place)) = triple.post() {
            let cap = self.pcg.capability_of(place, self.ctxt);
            let unpacked = cap.is_none()
                && self
                    .pcg
                    .place_capabilities
                    .capabilities_for_strict_postfixes_of(place)
                    .next()
                    .is_some();
            if cap == Some(CapabilityKind::Exclusive) || unpacked {
                self.record_and_apply_action(
                    BorrowPcgAction::freeze(place, "shared or two-phase borrow").into(),
                )?;
            } else {
                let ctxt = self.ctxt;
                pcg_validity_assert!(
                    cap == Some(CapabilityKind::Read),
                    [ctxt],
                    "{:?}: Borrowing {} for read with capability {:?}",
                    self.location(),
                    place.display_string(self.ctxt),
                    cap
                );
            }
        }
        Ok(())
    }
}
