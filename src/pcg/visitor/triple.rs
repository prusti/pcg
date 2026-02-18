use crate::{
    error::{PcgError, PcgUnsupportedError},
    pcg::{
        obtain::ObtainType,
        triple::{PlaceCondition, Triple},
    },
    utils::DataflowCtxt,
};

use super::PcgVisitor;

impl<'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PcgVisitor<'_, 'a, 'tcx, Ctxt> {
    #[tracing::instrument(skip(self))]
    pub(crate) fn require_triple(&mut self, triple: Triple<'tcx>) -> Result<(), PcgError<'tcx>> {
        match triple.pre() {
            PlaceCondition::ExpandTwoPhase(place) => {
                if place.contains_unsafe_deref(self.ctxt) {
                    return Err(PcgError::unsupported(PcgUnsupportedError::DerefUnsafePtr));
                }
                self.place_obtainer()
                    .obtain(place, ObtainType::TwoPhaseExpand)?;
            }
            PlaceCondition::Capability(place, capability) => {
                if place.contains_unsafe_deref(self.ctxt) {
                    return Err(PcgError::unsupported(PcgUnsupportedError::DerefUnsafePtr));
                }
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
            }
            PlaceCondition::Unalloc(_) | PlaceCondition::Return => {}
            PlaceCondition::RemoveCapability(_) => unreachable!(),
        }
        Ok(())
    }

    #[tracing::instrument(skip(self, triple), level = "warn")]
    pub(crate) fn ensure_triple(&mut self, triple: Triple<'tcx>) -> Result<(), PcgError<'tcx>> {
        self.pcg.ensure_triple(triple, self.ctxt);
        Ok(())
    }
}
