use crate::{
    error::PcgError,
    rustc_interface::middle::mir::PlaceElem,
    utils::{HasCompilerCtxt, Place},
};
pub trait PlaceProjectable<'tcx, Ctxt>: Sized {
    fn project_deeper(
        &self,
        elem: PlaceElem<'tcx>,
        ctxt: Ctxt,
    ) -> std::result::Result<Self, PcgError<'tcx>>;

    fn iter_projections(&self, ctxt: Ctxt) -> Vec<(Self, PlaceElem<'tcx>)>;
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> PlaceProjectable<'tcx, Ctxt> for Place<'tcx> {
    fn project_deeper(
        &self,
        elem: PlaceElem<'tcx>,
        ctxt: Ctxt,
    ) -> std::result::Result<Self, PcgError<'tcx>> {
        Place::project_deeper(*self, elem, ctxt).map_err(PcgError::unsupported)
    }
    fn iter_projections(&self, _ctxt: Ctxt) -> Vec<(Self, PlaceElem<'tcx>)> {
        self.0
            .iter_projections()
            .map(|(place, elem)| (place.into(), elem))
            .collect()
    }
}
