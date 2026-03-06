use crate::{
    borrow_pcg::graph::BorrowsGraph,
    owned_pcg::{
        OwnedExpansion, OwnedPcgLocal,
        node::{OwnedPcgInternalNode, OwnedPcgLeafNode, OwnedPcgNode},
        node_data::{MaterializedData, WithMaterialized},
    },
    pcg::OwnedCapability,
    rustc_interface::middle::mir::{self, Local},
    utils::{CompilerCtxt, Place, place::PlaceExpansion},
};

use crate::owned_pcg::RepackGuide;

use super::fpcs::OwnedPcg;

/// Build a materialized extension tree that expands `place` toward the given
/// `targets` (which are strict descendants of `place` referenced in the borrow PCG).
///
/// If no target has `place` as a strict prefix, returns a leaf with the given capability.
/// Otherwise, expands `place` and recurses into each child, filtering targets.
fn build_materialized_extension<'tcx>(
    place: Place<'tcx>,
    cap: OwnedCapability,
    targets: &[Place<'tcx>],
    ctxt: CompilerCtxt<'_, 'tcx>,
) -> OwnedPcgNode<'tcx, MaterializedData> {
    // Filter targets that are strict descendants of `place`
    let relevant: Vec<Place<'tcx>> = targets
        .iter()
        .copied()
        .filter(|t| place.is_strict_prefix_of(*t))
        .collect();

    if relevant.is_empty() {
        return OwnedPcgNode::Leaf(OwnedPcgLeafNode::with_data(cap, ()));
    }

    // Expand `place` using default guide
    let expansion: PlaceExpansion<'tcx> = place.expansion(RepackGuide::default(), ctxt);

    // For each child in the expansion, filter targets and recurse
    let child_entries: Vec<(mir::PlaceElem<'tcx>, OwnedPcgNode<'tcx, MaterializedData>)> =
        expansion
            .elems()
            .into_iter()
            .map(|elem| {
                let child_place = place.project_elem(elem, ctxt).unwrap();
                // Filter targets to those under this child
                let child_targets: Vec<Place<'tcx>> = relevant
                    .iter()
                    .copied()
                    .filter(|t| child_place.is_prefix_of(*t))
                    .collect();
                let child_node =
                    build_materialized_extension(child_place, cap, &child_targets, ctxt);
                (elem, child_node)
            })
            .collect();

    OwnedPcgNode::Internal(OwnedPcgInternalNode::new(OwnedExpansion::new(
        PlaceExpansion::from_vec(child_entries),
    )))
}

/// Recursively transform an init-state node into a `WithMaterialized` node.
///
/// For each leaf: checks if any borrow-owned place is a strict descendant and,
/// if so, builds a materialized extension tree as the leaf's `LeafData`.
fn materialize_node<'tcx>(
    node: &OwnedPcgNode<'tcx>,
    place: Place<'tcx>,
    borrow_owned: &[Place<'tcx>],
    ctxt: CompilerCtxt<'_, 'tcx>,
) -> OwnedPcgNode<'tcx, WithMaterialized> {
    match node {
        OwnedPcgNode::Leaf(leaf) => {
            // Check if any borrow-owned place is a strict descendant of this leaf
            let descendants: Vec<Place<'tcx>> = borrow_owned
                .iter()
                .copied()
                .filter(|t| place.is_strict_prefix_of(*t))
                .collect();

            let leaf_data = if descendants.is_empty() {
                None
            } else {
                Some(build_materialized_extension(
                    place,
                    leaf.capability,
                    &descendants,
                    ctxt,
                ))
            };

            OwnedPcgNode::Leaf(OwnedPcgLeafNode::with_data(leaf.capability, leaf_data))
        }
        OwnedPcgNode::Internal(internal) => {
            let child_entries: Vec<(
                mir::PlaceElem<'tcx>,
                OwnedPcgNode<'tcx, WithMaterialized>,
            )> = internal
                .expansion
                .data()
                .into_iter()
                .map(|(elem, child)| {
                    let child_place = place.project_elem(elem, ctxt).unwrap();
                    let child_node = materialize_node(child, child_place, borrow_owned, ctxt);
                    (elem, child_node)
                })
                .collect();

            OwnedPcgNode::Internal(OwnedPcgInternalNode::new(OwnedExpansion::new(
                PlaceExpansion::from_vec(child_entries),
            )))
        }
    }
}

impl<'tcx> OwnedPcg<'tcx> {
    /// Produce a materialized view of the owned PCG by extending init-state
    /// leaves to reach owned places referenced in the borrow PCG.
    pub(crate) fn materialize(
        &self,
        borrows: &BorrowsGraph<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Vec<(Local, OwnedPcgNode<'tcx, WithMaterialized>)> {
        let borrow_owned: Vec<Place<'tcx>> = borrows.owned_places(ctxt).into_iter().collect();

        self.iter_enumerated()
            .filter_map(|(local, local_pcg)| {
                let OwnedPcgLocal::Allocated(expansions) = local_pcg else {
                    return None;
                };
                let root_place: Place<'tcx> = local.into();
                let materialized =
                    materialize_node(expansions, root_place, &borrow_owned, ctxt);
                Some((local, materialized))
            })
            .collect()
    }
}
