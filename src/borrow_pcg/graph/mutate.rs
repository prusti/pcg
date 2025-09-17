use crate::{
    borrow_pcg::{
        action::LabelPlaceReason,
        edge_data::LabelEdgePlaces,
        graph::Conditioned,
        has_pcs_elem::PlaceLabeller,
        path_condition::{PathCondition, ValidityConditions},
    },
    rustc_interface::middle::mir::BasicBlock,
    utils::{CompilerCtxt, FilterMutResult, HasBorrowCheckerCtxt, Place},
};

use super::BorrowsGraph;

impl<'tcx, EdgeKind: LabelEdgePlaces<'tcx> + Eq + std::hash::Hash> BorrowsGraph<'tcx, EdgeKind> {
    pub(crate) fn label_place<'a>(
        &mut self,
        place: Place<'tcx>,
        reason: LabelPlaceReason,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        self.mut_edges(|edge| reason.apply_to_edge(place, &mut edge.value, labeller, ctxt))
    }
}

impl<'tcx> BorrowsGraph<'tcx> {
    pub(crate) fn filter_for_path(&mut self, path: &[BasicBlock], ctxt: CompilerCtxt<'_, 'tcx>) {
        self.edges
            .retain(|_, conditions| conditions.valid_for_path(path, ctxt.body()));
    }
}

impl<'tcx, EdgeKind> BorrowsGraph<'tcx, EdgeKind> {
    fn mut_edge_conditions(&mut self, mut f: impl FnMut(&mut ValidityConditions) -> bool) -> bool {
        let mut changed = false;
        for (_, conditions) in self.edges.iter_mut() {
            if f(conditions) {
                changed = true;
            }
        }
        changed
    }

    pub(crate) fn add_path_condition(
        &mut self,
        pc: PathCondition,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.mut_edge_conditions(|conditions| conditions.insert(pc, ctxt.body()))
    }

    pub(crate) fn mut_edges(
        &mut self,
        mut f: impl FnMut(&mut Conditioned<EdgeKind>) -> bool,
    ) -> bool
    where
        EdgeKind: Eq + std::hash::Hash + PartialEq,
    {
        let mut changed = false;
        self.edges = self
            .edges
            .drain()
            .map(|(kind, conditions)| {
                let mut edge = Conditioned::new(kind, conditions);
                if f(&mut edge) {
                    changed = true;
                }
                (edge.value, edge.conditions)
            })
            .collect();
        changed
    }

    pub(crate) fn filter_mut_edges(
        &mut self,
        mut f: impl FnMut(&mut Conditioned<EdgeKind>) -> FilterMutResult,
    ) -> bool
    where
        EdgeKind: Eq + std::hash::Hash + PartialEq,
    {
        let mut changed = false;
        self.edges = self
            .edges
            .drain()
            .filter_map(|(kind, conditions)| {
                let mut edge = Conditioned::new(kind, conditions);
                match f(&mut edge) {
                    FilterMutResult::Changed => {
                        changed = true;
                        Some((edge.value, edge.conditions))
                    }
                    FilterMutResult::Unchanged => Some((edge.value, edge.conditions)),
                    FilterMutResult::Remove => None,
                }
            })
            .collect();
        changed
    }
}
