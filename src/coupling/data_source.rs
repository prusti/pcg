use crate::{
    borrow_pcg::{
        borrow_pcg_edge::BorrowPcgEdge,
        edge::{abstraction::AbstractionEdge, kind::BorrowPcgEdgeKind},
        graph::{BorrowsGraph, Conditioned},
    },
    utils::data_structures::HashSet,
};

pub(crate) trait MutableCouplingDataSource<'tcx> {
    fn extract_abstraction_edges(&mut self) -> HashSet<Conditioned<AbstractionEdge<'tcx>>>;
}

pub(crate) trait CouplingDataSource<'tcx> {
    fn abstraction_edges(&self) -> HashSet<Conditioned<AbstractionEdge<'tcx>>>;
}

impl<'tcx> MutableCouplingDataSource<'tcx> for BorrowsGraph<'tcx> {
    fn extract_abstraction_edges(&mut self) -> HashSet<Conditioned<AbstractionEdge<'tcx>>> {
        let mut abstraction_edges = HashSet::default();
        self.edges.retain(|kind, conditions| match kind {
            BorrowPcgEdgeKind::Abstraction(abstraction) => {
                abstraction_edges.insert(Conditioned::new(abstraction.clone(), conditions.clone()));
                false
            }
            _ => true,
        });
        abstraction_edges
    }
}

impl<'tcx> MutableCouplingDataSource<'tcx> for HashSet<BorrowPcgEdge<'tcx>> {
    fn extract_abstraction_edges(&mut self) -> HashSet<Conditioned<AbstractionEdge<'tcx>>> {
        let mut abstraction_edges = HashSet::default();
        self.retain(|edge| match edge.kind() {
            BorrowPcgEdgeKind::Abstraction(abstraction) => {
                abstraction_edges.insert(Conditioned::new(
                    abstraction.clone(),
                    edge.conditions().clone(),
                ));
                false
            }
            _ => true,
        });
        abstraction_edges
    }
}

impl<'tcx> CouplingDataSource<'tcx> for BorrowsGraph<'tcx> {
    fn abstraction_edges(&self) -> HashSet<Conditioned<AbstractionEdge<'tcx>>> {
        self.edges
            .iter()
            .filter_map(|(kind, conditions)| match kind {
                BorrowPcgEdgeKind::Abstraction(abstraction) => {
                    Some(Conditioned::new(abstraction.clone(), conditions.clone()))
                }
                _ => None,
            })
            .collect()
    }
}
