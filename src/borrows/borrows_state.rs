use crate::rustc_interface::{
    ast::Mutability,
    data_structures::fx::FxHashSet,
    middle::mir::{BasicBlock, Location},
    middle::ty::{self},
};
use serde_json::{json, Value};

use crate::{
    free_pcs::CapabilityKind,
    utils::{Place, PlaceRepacker, SnapshotLocation},
    BorrowsBridge, Weaken,
};

use super::{
    borrow_edge::BorrowEdge,
    borrow_pcg_capabilities::BorrowPCGCapabilities,
    borrow_pcg_edge::{BlockedNode, BorrowPCGEdge, BorrowPCGEdgeKind, PCGNode, ToBorrowsEdge},
    borrows_graph::{BorrowsGraph, Conditioned},
    borrows_visitor::DebugCtx,
    coupling_graph_constructor::LivenessChecker,
    deref_expansion::DerefExpansion,
    domain::{AbstractionType, MaybeOldPlace, MaybeRemotePlace},
    has_pcs_elem::HasPcsElems,
    latest::Latest,
    path_condition::{PathCondition, PathConditions},
    region_abstraction::AbstractionEdge,
    region_projection_member::{RegionProjectionMember, RegionProjectionMemberDirection},
    unblock_graph::UnblockGraph,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BorrowsState<'tcx> {
    pub latest: Latest<'tcx>,
    graph: BorrowsGraph<'tcx>,
    capabilities: BorrowPCGCapabilities<'tcx>,
}

impl<'tcx> BorrowsState<'tcx> {
    pub fn contains<T: Into<PCGNode<'tcx>>>(
        &self,
        node: T,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        self.graph.contains(node.into(), repacker)
    }
    pub fn capabilities(&self) -> &BorrowPCGCapabilities<'tcx> {
        &self.capabilities
    }

    pub fn graph_edges(&self) -> impl Iterator<Item = &BorrowPCGEdge<'tcx>> {
        self.graph.edges()
    }

    pub fn graph(&self) -> &BorrowsGraph<'tcx> {
        &self.graph
    }

    pub fn get_capability<T: Into<PCGNode<'tcx>>>(&self, node: T) -> Option<CapabilityKind> {
        self.capabilities.get(node.into())
    }

    pub fn set_capability<T: Into<PCGNode<'tcx>>>(&mut self, node: T, capability: CapabilityKind) {
        self.capabilities.insert(node, capability);
    }

    pub fn join<'mir, T: LivenessChecker<'tcx>>(
        &mut self,
        other: &Self,
        self_block: BasicBlock,
        other_block: BasicBlock,
        region_liveness: &T,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let mut changed = false;
        if self.graph.join(
            &other.graph,
            self_block,
            other_block,
            repacker,
            region_liveness,
        ) {
            changed = true;
        }
        if self.latest.join(&other.latest, self_block) {
            // TODO: Setting changed to true prevents divergence for loops,
            // think about how latest should work in loops

            // changed = true;
        }
        if self.capabilities.join(&other.capabilities) {
            changed = true;
        }
        changed
    }

    pub fn change_pcs_elem<T: 'tcx>(&mut self, old: T, new: T) -> bool
    where
        T: PartialEq + Clone,
        BorrowPCGEdge<'tcx>: HasPcsElems<T>,
    {
        self.graph.change_pcs_elem(old, new)
    }

    fn remove_edge_and_set_latest(
        &mut self,
        edge: &BorrowPCGEdge<'tcx>,
        location: Location,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        if !edge.is_shared_borrow() {
            for place in edge.blocked_places(repacker) {
                if let Some(place) = place.as_current_place() {
                    self.set_latest(place, location)
                }
            }
        }
        self.graph.remove(edge, DebugCtx::new(location))
    }

    pub fn borrow_edges_reserved_at(
        &self,
        location: Location,
    ) -> FxHashSet<Conditioned<BorrowEdge<'tcx>>> {
        self.graph
            .edges()
            .filter_map(|edge| match &edge.kind() {
                BorrowPCGEdgeKind::Borrow(borrow) if borrow.reserve_location() == location => {
                    Some(Conditioned {
                        conditions: edge.conditions().clone(),
                        value: borrow.clone(),
                    })
                }
                _ => None,
            })
            .collect()
    }

    /// Collapses nodes using the following rules:
    /// - If a node is only blocked by old leaves, then the node should be collapsed
    /// - If a PCS node's expansion is only leaves, the node should be collapsed
    /// This function performs such collapses until a fixpoint is reached
    pub fn minimize(&mut self, repacker: PlaceRepacker<'_, 'tcx>, location: Location) {
        loop {
            let edges = self.graph.edges().cloned().collect::<Vec<_>>();
            let num_edges_prev = edges.len();
            let to_remove = edges
                .into_iter()
                .filter(|edge| {
                    let is_old_unblocked = edge
                        .blocked_by_nodes(repacker)
                        .iter()
                        .all(|p| p.is_old() && !self.graph.has_edge_blocking(*p, repacker));
                    is_old_unblocked
                        || match &edge.kind() {
                            BorrowPCGEdgeKind::DerefExpansion(de) => {
                                !de.is_owned_expansion()
                                    && de
                                        .expansion(repacker)
                                        .into_iter()
                                        .all(|p| !self.graph.has_edge_blocking(p, repacker))
                            }
                            _ => false,
                        }
                })
                .collect::<Vec<_>>();
            if to_remove.is_empty() {
                break;
            }
            for edge in to_remove {
                self.remove_edge_and_set_latest(&edge, location, repacker);
            }
            assert!(self.graph.edge_count() < num_edges_prev);
        }
    }

    pub fn add_path_condition(&mut self, pc: PathCondition) -> bool {
        self.graph.add_path_condition(pc)
    }

    pub fn filter_for_path(&mut self, path: &[BasicBlock]) {
        self.graph.filter_for_path(path);
    }

    pub fn insert_owned_expansion(&mut self, place: MaybeOldPlace<'tcx>, location: Location) {
        self.graph.insert_owned_expansion(place, location);
    }

    pub fn borrows_blocking_prefix_of(
        &self,
        place: Place<'tcx>,
    ) -> FxHashSet<Conditioned<BorrowEdge<'tcx>>> {
        self.borrows()
            .into_iter()
            .filter(|rb| match rb.value.blocked_place {
                MaybeRemotePlace::Local(MaybeOldPlace::Current {
                    place: blocked_place,
                }) => blocked_place.is_prefix(place),
                _ => false,
            })
            .collect()
    }

    pub fn delete_descendants_of(
        &mut self,
        place: MaybeOldPlace<'tcx>,
        location: Location,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let edges = self.edges_blocking(place.into(), repacker);
        if edges.is_empty() {
            return false;
        }
        for edge in edges {
            self.remove_edge_and_set_latest(&edge, location, repacker);
        }
        true
    }

    pub fn get_place_blocking(
        &self,
        place: MaybeRemotePlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Option<MaybeOldPlace<'tcx>> {
        let edges = self.edges_blocking(place.into(), repacker);
        if edges.len() != 1 {
            return None;
        }
        match edges[0].kind() {
            BorrowPCGEdgeKind::Borrow(reborrow) => Some(reborrow.assigned_place),
            BorrowPCGEdgeKind::DerefExpansion(_) => todo!(),
            BorrowPCGEdgeKind::Abstraction(_) => todo!(),
            BorrowPCGEdgeKind::RegionProjectionMember(_) => todo!(),
        }
    }

    pub fn edges_blocking(
        &self,
        node: BlockedNode<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<BorrowPCGEdge<'tcx>> {
        self.graph.edges_blocking(node, repacker)
    }

    pub fn deref_expansions(&self) -> FxHashSet<Conditioned<DerefExpansion<'tcx>>> {
        self.graph.deref_expansions()
    }

    pub fn move_region_projection_member_projections(
        &mut self,
        old_projection_place: MaybeOldPlace<'tcx>,
        new_projection_place: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        self.graph.move_region_projection_member_projections(
            old_projection_place,
            new_projection_place,
            repacker,
        );
    }

    pub fn move_borrows(
        &mut self,
        orig_assigned_place: MaybeOldPlace<'tcx>,
        new_assigned_place: MaybeOldPlace<'tcx>,
    ) {
        self.graph
            .move_borrows(orig_assigned_place, new_assigned_place);
    }

    pub fn borrows_blocked_by(
        &self,
        place: MaybeOldPlace<'tcx>,
    ) -> FxHashSet<Conditioned<BorrowEdge<'tcx>>> {
        self.graph.borrows_blocked_by(place)
    }

    pub fn borrows(&self) -> FxHashSet<Conditioned<BorrowEdge<'tcx>>> {
        self.graph.borrows()
    }

    pub fn bridge(
        &self,
        to: &Self,
        _debug_ctx: DebugCtx,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> BorrowsBridge<'tcx> {
        let added_borrows: FxHashSet<Conditioned<BorrowEdge<'tcx>>> = to
            .borrows()
            .into_iter()
            .filter(|rb| !self.has_reborrow_at_location(rb.value.reserve_location()))
            .collect();

        let expands = to
            .deref_expansions()
            .difference(&self.deref_expansions())
            .cloned()
            .collect();

        let mut ug = UnblockGraph::new();

        for borrow in self.borrows() {
            if !to.has_reborrow_at_location(borrow.value.reserve_location()) {
                ug.kill_edge(borrow.clone().into(), self, repacker);
            }
        }

        for exp in self.deref_expansions().difference(&to.deref_expansions()) {
            ug.kill_edge(exp.clone().into(), self, repacker);
        }

        for abstraction in self.region_abstractions() {
            if !to.region_abstractions().contains(&abstraction) {
                ug.kill_edge(abstraction.clone().into(), self, repacker);
            }
        }

        let mut weakens: FxHashSet<Weaken<'tcx>> = FxHashSet::default();

        for (place, capability) in self.capabilities.place_capabilities() {
            if let Some(to_capability) = to.capabilities.get(place) {
                if capability > to_capability {
                    weakens.insert(Weaken(place.clone(), capability, to_capability));
                }
            }
        }

        BorrowsBridge {
            added_borrows,
            expands,
            ug,
            weakens,
        }
    }

    /// Ensures that the place is expanded to exactly the given place. If
    /// `capability` is `Some`, the capability of the expanded place is set to
    /// the given value.
    pub fn ensure_expansion_to_exactly(
        &mut self,
        repacker: PlaceRepacker<'_, 'tcx>,
        node: BlockedNode<'tcx>,
        location: Location,
        capability: Option<CapabilityKind>,
    ) {
        let mut ug = UnblockGraph::new();
        let graph_edges = self.graph.edges().cloned().collect::<Vec<_>>();
        if let Some(place) = node.as_current_place() {
            for p in graph_edges {
                match p.kind() {
                    BorrowPCGEdgeKind::Borrow(reborrow) => match reborrow.assigned_place {
                        MaybeOldPlace::Current {
                            place: assigned_place,
                        } if place.is_prefix(assigned_place) && !place.is_ref(repacker) => {
                            for ra in place.region_projections(repacker) {
                                self.add_region_projection_member(
                                    RegionProjectionMember::new(
                                        reborrow.blocked_place,
                                        ra,
                                        RegionProjectionMemberDirection::ProjectionBlocksPlace,
                                    ),
                                    PathConditions::new(location.block),
                                    repacker,
                                );
                            }
                        }
                        _ => {}
                    },
                    _ => {}
                }
            }
        }
        ug.unblock_node(node, self, repacker);
        self.apply_unblock_graph(ug, repacker, location);

        // Originally we may not have been expanded enough
        if let Some(place) = node.as_current_place() {
            if let Some(inherent_cap) =
                self.graph
                    .ensure_deref_expansion_to_at_least(place.into(), repacker, location)
            {
                self.capabilities.insert(place, inherent_cap);
            }
        }
        if let Some(capability) = capability {
            self.capabilities.insert(node, capability);
        }
    }

    pub fn roots(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<MaybeRemotePlace<'tcx>> {
        self.graph.roots(repacker)
    }

    pub fn kill_borrows(
        &mut self,
        reserve_location: Location,
        kill_location: Location,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let edges_to_remove = self.borrow_edges_reserved_at(reserve_location);
        if edges_to_remove.is_empty() {
            return false;
        }
        for edge in edges_to_remove {
            if edge.value.is_mut() {
                self.set_capability(edge.value.assigned_ref(repacker), CapabilityKind::Write)
            }
            self.remove_edge_and_set_latest(&edge.into(), kill_location, repacker);
        }
        true
    }

    pub fn apply_unblock_graph(
        &mut self,
        graph: UnblockGraph<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        location: Location,
    ) -> bool {
        let mut changed = false;
        for action in graph.actions(repacker) {
            match action {
                crate::combined_pcs::UnblockAction::TerminateBorrow {
                    reserve_location, ..
                } => {
                    if self.kill_borrows(reserve_location, location, repacker) {
                        changed = true;
                    }
                }
                crate::combined_pcs::UnblockAction::Collapse(place, _) => {
                    if self.delete_descendants_of(place, location, repacker) {
                        changed = true;
                    }
                }
                crate::combined_pcs::UnblockAction::TerminateAbstraction(location, _call) => {
                    self.graph.remove_abstraction_at(location);
                }
                crate::combined_pcs::UnblockAction::TerminateRegionProjectionMember(
                    region_projection_member,
                ) => {
                    self.graph
                        .remove_region_projection_member(region_projection_member);
                }
            }
        }
        changed
    }

    pub fn set_latest<T: Into<SnapshotLocation>>(&mut self, place: Place<'tcx>, location: T) {
        self.latest.insert(place, location.into());
    }

    pub fn get_latest(&self, place: Place<'tcx>) -> SnapshotLocation {
        self.latest.get(place)
    }

    pub fn add_region_projection_member(
        &mut self,
        member: RegionProjectionMember<'tcx>,
        pc: PathConditions,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        self.graph.insert(member.clone().to_borrow_pcg_edge(pc));
        let (place_cap, proj_cap) = if member.mutability(repacker) == Mutability::Mut {
            match member.direction() {
                RegionProjectionMemberDirection::ProjectionBlocksPlace => {
                    (CapabilityKind::Exclusive, CapabilityKind::Lent)
                }
                RegionProjectionMemberDirection::PlaceBlocksProjection => {
                    (CapabilityKind::Lent, CapabilityKind::Exclusive)
                }
            }
        } else {
            (CapabilityKind::Read, CapabilityKind::Read)
        };
        self.set_capability(member.place, place_cap);
        self.set_capability(member.projection, proj_cap);
    }

    pub fn trim_old_leaves(&mut self, repacker: PlaceRepacker<'_, 'tcx>, location: Location) {
        loop {
            let mut cont = false;
            let edges = self.graph.leaf_edges(repacker);
            for edge in edges {
                if edge.blocked_by_nodes(repacker).iter().all(|p| p.is_old()) {
                    self.remove_edge_and_set_latest(&edge, location, repacker);
                    cont = true;
                }
            }
            if !cont {
                break;
            }
        }
    }

    pub fn add_borrow(
        &mut self,
        blocked_place: MaybeRemotePlace<'tcx>,
        assigned_place: Place<'tcx>,
        mutability: Mutability,
        location: Location,
        region: ty::Region<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        let (blocked_cap, assigned_cap) = match mutability {
            Mutability::Not => (CapabilityKind::Read, CapabilityKind::Read),
            Mutability::Mut => (CapabilityKind::Lent, CapabilityKind::Exclusive),
        };
        let borrow_edge = BorrowEdge::new(
            blocked_place.into(),
            assigned_place.into(),
            mutability,
            location,
            region,
        );
        if let Some(rp) = borrow_edge.assigned_region_projection(repacker) {
            self.graph.insert(
                RegionProjectionMember::new(
                    assigned_place.into(),
                    rp,
                    RegionProjectionMemberDirection::PlaceBlocksProjection,
                )
                .to_borrow_pcg_edge(PathConditions::new(location.block)),
            );
            self.set_capability(rp, blocked_cap);
            if rp.place.is_ref(repacker) {
                self.graph.insert_owned_expansion(rp.place, location);
            }
        }
        self.graph
            .insert(borrow_edge.to_borrow_pcg_edge(PathConditions::AtBlock(location.block)));

        if !blocked_place.is_owned(repacker) {
            self.set_capability(blocked_place, blocked_cap);
        }
        self.set_capability(assigned_place, assigned_cap);
    }

    pub fn has_reborrow_at_location(&self, location: Location) -> bool {
        self.graph.has_borrow_at_location(location)
    }

    pub fn region_abstractions(&self) -> FxHashSet<Conditioned<AbstractionEdge<'tcx>>> {
        self.graph.abstraction_edges()
    }

    pub fn to_json(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> Value {
        json!({})
    }

    pub fn new() -> Self {
        Self {
            latest: Latest::new(),
            graph: BorrowsGraph::new(),
            capabilities: BorrowPCGCapabilities::new(),
        }
    }

    pub fn add_region_abstraction(
        &mut self,
        abstraction: AbstractionEdge<'tcx>,
        block: BasicBlock,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        match &abstraction.abstraction_type {
            AbstractionType::FunctionCall(function_call_abstraction) => {
                for edge in function_call_abstraction.edges() {
                    for input in edge.inputs() {
                        self.set_capability(input, CapabilityKind::Lent);
                    }
                    for output in edge.outputs() {
                        self.set_capability(output, CapabilityKind::Exclusive);
                        if output.place.is_ref(repacker) {
                            self.graph.insert_owned_expansion(
                                output.place,
                                function_call_abstraction.location(),
                            );
                        }
                    }
                }
            }
            _ => {}
        }
        self.graph
            .insert(abstraction.to_borrow_pcg_edge(PathConditions::new(block)));
    }

    pub fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        _repacker: PlaceRepacker<'_, 'tcx>,
        debug_ctx: Option<DebugCtx>,
    ) {
        self.graph.make_place_old(place, &self.latest, debug_ctx);
    }
}
