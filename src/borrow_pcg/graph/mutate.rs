use crate::{
    borrow_pcg::{
        action::LabelPlaceReason,
        edge_data::{LabelEdgePlaces, NodeReplacement},
        graph::Conditioned,
        has_pcs_elem::PlaceLabeller,
        validity_conditions::{PathCondition, ValidityConditionOps, ValidityConditions},
    },
    rustc_interface::middle::mir::BasicBlock,
    utils::{
        CompilerCtxt, FilterMutResult, PcgPlace,
        data_structures::{HashMap, HashSet},
    },
};

use std::collections::hash_map;

use super::BorrowsGraph;

impl<'tcx> BorrowsGraph<'tcx> {
    pub(crate) fn filter_for_path(&mut self, path: &[BasicBlock], ctxt: CompilerCtxt<'_, 'tcx>) {
        self.edges
            .retain(|_, conditions| conditions.valid_for_path(path, ctxt.body()));
    }
}

/// Insert `edge` into `edges`, joining validity conditions if an identical
/// edge kind is already present. Edge mutations (e.g. unlabelling lifetime
/// projections) can make two conditional edges identical; their conditions
/// must be joined, not overwritten.
fn insert_joining_conditions<EdgeKind: Eq + std::hash::Hash, VC, Ctxt: Copy>(
    edges: &mut HashMap<EdgeKind, VC>,
    edge: Conditioned<EdgeKind, VC>,
    ctxt: Ctxt,
) where
    VC: ValidityConditionOps<Ctxt>,
{
    match edges.entry(edge.value) {
        hash_map::Entry::Occupied(mut existing) => {
            existing.get_mut().join(&edge.conditions, ctxt);
        }
        hash_map::Entry::Vacant(slot) => {
            slot.insert(edge.conditions);
        }
    }
}

impl<'tcx, EdgeKind> BorrowsGraph<'tcx, EdgeKind> {
    fn mut_edge_conditions(&mut self, mut f: impl FnMut(&mut ValidityConditions) -> bool) -> bool {
        let mut changed = false;
        for conditions in self.edges.values_mut() {
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
}

impl<'tcx, EdgeKind, VC> BorrowsGraph<'tcx, EdgeKind, VC> {
    pub(crate) fn mut_edges<Ctxt: Copy>(
        &mut self,
        mut f: impl FnMut(&mut Conditioned<EdgeKind, VC>) -> bool,
        ctxt: Ctxt,
    ) -> bool
    where
        EdgeKind: Eq + std::hash::Hash + PartialEq,
        VC: ValidityConditionOps<Ctxt>,
    {
        let mut changed = false;
        let mut new_edges = HashMap::default();
        for (kind, conditions) in self.edges.drain() {
            let mut edge = Conditioned::new(kind, conditions);
            if f(&mut edge) {
                changed = true;
            }
            insert_joining_conditions(&mut new_edges, edge, ctxt);
        }
        self.edges = new_edges;
        changed
    }

    pub(crate) fn filter_mut_edges<Ctxt: Copy>(
        &mut self,
        mut f: impl FnMut(&mut Conditioned<EdgeKind, VC>) -> FilterMutResult,
        ctxt: Ctxt,
    ) -> bool
    where
        EdgeKind: Eq + std::hash::Hash + PartialEq,
        VC: ValidityConditionOps<Ctxt>,
    {
        let mut changed = false;
        let mut new_edges = HashMap::default();
        for (kind, conditions) in self.edges.drain() {
            let mut edge = Conditioned::new(kind, conditions);
            match f(&mut edge) {
                FilterMutResult::Changed => {
                    changed = true;
                    insert_joining_conditions(&mut new_edges, edge, ctxt);
                }
                FilterMutResult::Unchanged => {
                    insert_joining_conditions(&mut new_edges, edge, ctxt);
                }
                FilterMutResult::Remove => {}
            }
        }
        self.edges = new_edges;
        changed
    }
    pub(crate) fn label_place<P: PcgPlace<'tcx, Ctxt>, Ctxt: Copy>(
        &mut self,
        place: P,
        reason: LabelPlaceReason,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>>
    where
        EdgeKind: LabelEdgePlaces<'tcx, Ctxt, P> + Eq + std::hash::Hash,
        VC: ValidityConditionOps<Ctxt>,
    {
        let mut all_replacements = HashSet::default();
        self.mut_edges(
            |edge| {
                let replacements = reason.apply_to_edge(place, &mut edge.value, labeller, ctxt);
                let changed = !replacements.is_empty();
                all_replacements.extend(replacements);
                changed
            },
            ctxt,
        );
        all_replacements
    }
}
