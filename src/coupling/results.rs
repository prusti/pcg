use crate::{
    borrow_pcg::{edge::abstraction::AbstractionEdge, graph::Conditioned},
    coupling::{CouplingError, MaybeCoupledEdges, PcgCoupledEdges},
    utils::data_structures::HashSet,
};
use derive_more::Deref;

/// All results from an application of the coupling algorithm over a set of
/// abstraction edges
pub struct CouplingResults<'tcx, Err>(Vec<CoupleEdgesResult<'tcx, Err>>);

pub(crate) type PcgCouplingResults<'tcx> =
    CouplingResults<'tcx, Vec<Conditioned<AbstractionEdge<'tcx>>>>;

impl<'tcx, SourceData> CouplingResults<'tcx, SourceData> {
    pub(crate) fn new(results: Vec<CoupleEdgesResult<'tcx, SourceData>>) -> Self {
        Self(results)
    }

    pub(crate) fn into_iter(self) -> impl Iterator<Item = CoupleEdgesResult<'tcx, SourceData>> {
        self.0.into_iter()
    }
}

impl<'tcx> PcgCouplingResults<'tcx> {
    pub(crate) fn into_maybe_coupled_edges(
        self,
    ) -> HashSet<MaybeCoupledEdges<'tcx, Conditioned<AbstractionEdge<'tcx>>>> {
        self.into_iter()
            .map(|result| match result.0 {
                Ok(result) => MaybeCoupledEdges::Coupled(Box::new(result)),
                Err(other) => MaybeCoupledEdges::NotCoupled(other.source_data),
            })
            .collect()
    }
}

/// Either all of the coupled edges for a function or loop, or an error
#[derive(Eq, Hash, PartialEq, Clone, Debug, Deref)]
pub(crate) struct CoupleEdgesResult<'tcx, SourceEdges>(
    pub(crate) Result<PcgCoupledEdges<'tcx>, CouplingError<SourceEdges>>,
);

pub(crate) type PcgCoupleEdgesResult<'tcx> =
    CoupleEdgesResult<'tcx, Vec<Conditioned<AbstractionEdge<'tcx>>>>;

impl<'tcx, SourceEdges> CoupleEdgesResult<'tcx, SourceEdges> {
    pub(crate) fn map_source_edges<T>(
        self,
        f: impl FnOnce(SourceEdges) -> T,
    ) -> CoupleEdgesResult<'tcx, T> {
        CoupleEdgesResult(self.0.map_err(|e| e.map_source_data(f)))
    }
}
