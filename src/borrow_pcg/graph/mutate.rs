use crate::{
    borrow_pcg::{
        action::LabelPlaceReason,
        edge_data::{LabelEdgePlaces, NodeReplacement},
        graph::Conditioned,
        has_pcs_elem::PlaceLabeller,
        validity_conditions::{PathCondition, ValidityConditions},
    },
    rustc_interface::middle::mir::BasicBlock,
    utils::{CompilerCtxt, FilterMutResult, HasBorrowCheckerCtxt, data_structures::HashSet},
};

use super::BorrowsGraph;

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
    pub(crate) fn label_place<P: std::hash::Hash + Eq + Copy, Ctxt: Copy>(
        &mut self,
        place: P,
        reason: LabelPlaceReason,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>>
    where
        EdgeKind: LabelEdgePlaces<'tcx, Ctxt, P> + Eq + std::hash::Hash,
    {
        let mut all_replacements = HashSet::default();
        self.mut_edges(|edge| {
            let replacements = reason.apply_to_edge(place, &mut edge.value, labeller, ctxt);
            let changed = !replacements.is_empty();
            all_replacements.extend(replacements);
            changed
        });
        all_replacements
    }
}
