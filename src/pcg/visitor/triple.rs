use crate::{
    error::PcgError,
    pcg::triple::{PlacePrecondition, Triple},
    utils::DataflowCtxt,
};

use super::PcgVisitor;

impl<'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PcgVisitor<'_, 'a, 'tcx, Ctxt> {
    #[tracing::instrument(skip(self))]
    pub(crate) fn require_triple(&mut self, triple: &Triple<'tcx>) -> Result<(), PcgError<'tcx>> {
        self.require(triple.pre())
    }

    pub(crate) fn require(
        &mut self,
        place_precondition: &PlacePrecondition<'tcx>,
    ) -> Result<(), PcgError<'tcx>> {
        match place_precondition {
            PlacePrecondition::Capability(place, cap) => {
                self.place_obtainer().obtain(*place, *cap)
            }
            PlacePrecondition::True => {
                Ok(())
            }
            PlacePrecondition::IfAllocated(local, place_precondition) => {
                if self.pcg.owned.is_allocated(*local) {
                    self.require(place_precondition)
                } else {
                    Ok(())
                }
            }
        }
    }

    #[tracing::instrument(skip(self, triple), level = "warn")]
    pub(crate) fn ensure_triple(&mut self, triple: &Triple<'tcx>) -> Result<(), PcgError<'tcx>> {
        self.pcg.ensure_triple(triple, self.ctxt);
        Ok(())
    }
}
