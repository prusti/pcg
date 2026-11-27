use std::borrow::Cow;

use super::PcgError;
use crate::{
    action::BorrowPcgAction,
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike, LocalNode},
        borrow_pcg_expansion::BorrowPcgExpansion,
        edge::{
            borrow_flow::{BorrowFlowEdgeKind, private::FutureEdgeKind},
            deref::DerefEdge,
            kind::BorrowPcgEdgeKind,
        },
        edge_data::EdgeData,
        graph::{Conditioned, frozen::FrozenGraphRef},
        region_projection::{LifetimeProjectionLabel, LocalLifetimeProjection, PlaceOrConst},
    },
    pcg::{
        CapabilityKind, PcgNode, PcgRefLike,
        obtain::{PlaceCollapser, PlaceObtainer},
    },
    utils::{
        DataflowCtxt, DebugCtxt, HasPlace, PackStrategy, Place,
        data_structures::{HashMap, HashSet},
        display::DisplayWithCompilerCtxt,
        maybe_old::MaybeLabelledPlace,
        place::maybe_remote::MaybeRemotePlace,
    },
};

type Reason = Cow<'static, str>;

#[allow(clippy::large_enum_variant)]
enum RemovalAction<'tcx> {
    RemoveDerefEdgesTo(
        MaybeLabelledPlace<'tcx>,
        HashSet<Conditioned<DerefEdge<'tcx>>>,
        Reason,
    ),
    RemoveOtherEdge(BorrowPcgEdge<'tcx>, Reason),
}

impl<'pcg, 'a: 'pcg, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx> + DebugCtxt>
    PlaceObtainer<'pcg, 'a, 'tcx, Ctxt>
{
    /// Removes leaves that are old or dead (based on the borrow checker). This
    /// function should called prior to evaluating the effect of the statement
    /// at `location`.
    ///
    /// Note that the liveness calculation is performed based on what happened
    /// at the end of the *previous* statement.
    ///
    /// For example when evaluating:
    /// ```text
    /// bb0[1]: let x = &mut y;
    /// bb0[2]: *x = 2;
    /// bb0[3]: ... // x is dead
    /// ```
    /// we do not remove the `*x -> y` edge until `bb0[3]`.
    /// This ensures that the edge appears in the graph at the end of `bb0[2]`
    /// (rather than never at all).
    ///
    /// Additional caveat: we do not remove dead places that are function
    /// arguments. At least for now this interferes with the implementation in
    /// the Prusti purified encoding for accessing the final value of a
    /// reference-typed function argument in its postcondition.
    pub(crate) fn pack_old_and_dead_borrow_leaves(
        &mut self,
        for_place: Option<Place<'tcx>>,
    ) -> Result<(), PcgError> {
        let debug_iteration_limit = 10000;
        let mut iteration = 0;
        let ctxt = self.ctxt;
        let block = self.location().block;
        self.restore_capability_to_leaf_places(
            for_place,
            |place| !ctxt.body_analysis().is_read_only_in_loop(block, place),
            ctxt,
        )?;
        let mut removed_edges = Vec::new();
        loop {
            iteration += 1;
            // A removal can label places and lifetime projections, which
            // changes the edges that contain them, and can change capabilities.
            // So each removal is identified in the graph the previous one left.
            let Some(action) = self.identify_leaf_edges_to_remove(for_place) else {
                self.merge_settled_snapshots()?;
                break self.finish_weakening_places_with_dead_lifetime_projections(&removed_edges);
            };
            match action {
                RemovalAction::RemoveDerefEdgesTo(place, edges, reason) => {
                    self.remove_deref_edges_to(place, edges, &reason)?;
                }
                RemovalAction::RemoveOtherEdge(borrow_pcg_edge, reason) => {
                    self.remove_edge_and_perform_associated_state_updates(
                        &borrow_pcg_edge,
                        &reason,
                    )?;
                    removed_edges.push(borrow_pcg_edge);
                }
            }
            if iteration % 10 == 0 {
                tracing::debug!(
                    "Packing old and dead borrow leaves: iteration {}",
                    iteration
                );
            }
            assert!(
                iteration <= debug_iteration_limit,
                "Packing old and dead borrow leaves took more than {debug_iteration_limit} iterations"
            );
        }
    }

    /// Cuts the delegations that keep a loan of `place` alive.
    ///
    /// A delegation stays alive for as long as its raw pointer is used, which
    /// also keeps alive the borrows leading to it. The borrow checker doesn't
    /// see this: for `let r = &mut x; let p = r as *mut i32; x = 1; *p = 2;` it
    /// accepts the access to `x`, since `r` is dead. Such an access invalidates
    /// the raw pointers derived from the loan, so the delegations are removed:
    /// the raw pointers no longer give access to the loaned place. The raw
    /// pointers keep their own capability, since their values stay valid (`p`
    /// can still be copied). A delegation of `place` itself is unaffected, since
    /// `place` is not lent out to the raw pointer.
    pub(crate) fn cut_delegations_through_loans_of(
        &mut self,
        place: Place<'tcx>,
        obtain_cap: CapabilityKind,
    ) -> Result<(), PcgError> {
        let has_capability = match self.pcg.capability_of(place, self.ctxt) {
            None => false,
            Some(CapabilityKind::Read) => obtain_cap.is_read(),
            Some(_) => true,
        };
        if has_capability {
            return Ok(());
        }
        let delegations = self.delegations_through_loans_of(place);
        if delegations.is_empty() {
            return Ok(());
        }
        let context = format!(
            "Delegation is cut because access to {} is needed",
            place.display_string(self.ctxt)
        );
        for edge in delegations {
            self.record_and_apply_action(
                BorrowPcgAction::remove_edge(edge, context.clone()).into(),
            )?;
        }
        self.pack_old_and_dead_borrow_leaves(None)
    }

    /// The delegation edges that (transitively) block a loan of `place`, or of
    /// a place overlapping with it.
    ///
    /// If `place` is reached through a raw pointer, i.e. it lies below the
    /// raw-pointer side of a delegation, the access also goes to the memory of
    /// the delegation's aliased place. The raw pointer carries the provenance
    /// of that place, so loans of it are treated like loans of `place`: for
    /// `let r = &mut x; let p = r as *mut i32; let r2 = &mut *r;
    /// let p2 = r2 as *mut i32; *p = 1; *p2 = 2;` the write through `p` is a
    /// write to `*r`, which invalidates `p2`.
    ///
    /// The whole aliased place is used rather than the corresponding subplace,
    /// since a pointer cast may have changed the pointee type. This can only
    /// cut more delegations, never fewer.
    fn delegations_through_loans_of(&self, place: Place<'tcx>) -> Vec<BorrowPcgEdge<'tcx>> {
        let ctxt = self.ctxt.bc_ctxt();
        let graph = self.pcg.borrows_graph();
        // Delegations always point to the original, non-raw place (copies and
        // casts of raw pointers propagate it), so no transitive search is needed.
        let accessed = std::iter::once(place)
            .chain(graph.edges().filter_map(|edge| {
                let BorrowPcgEdgeKind::Delegation(delegation) = edge.kind else {
                    return None;
                };
                let rawptr = delegation.rawptr_place.as_current_place()?;
                if rawptr.is_prefix_of(place) {
                    delegation.aliased_place.as_current_place()
                } else {
                    None
                }
            }))
            .collect::<Vec<_>>();
        let mut worklist = graph
            .edges()
            .filter(|edge| {
                let BorrowPcgEdgeKind::Borrow(borrow) = edge.kind else {
                    return false;
                };
                borrow
                    .blocked_place
                    .as_current_place()
                    .is_some_and(|blocked| {
                        accessed
                            .iter()
                            .any(|&accessed| blocked.conflicts_with(accessed))
                    })
            })
            .map(BorrowPcgEdgeLike::to_owned_edge)
            .collect::<Vec<_>>();
        let mut seen = HashSet::default();
        let mut delegations = Vec::new();
        while let Some(edge) = worklist.pop() {
            if !seen.insert(edge.clone()) {
                continue;
            }
            if matches!(edge.kind(), BorrowPcgEdgeKind::Delegation(_)) {
                delegations.push(edge);
                continue;
            }
            for node in edge.blocked_by_nodes(ctxt) {
                worklist.extend(
                    graph
                        .edges_blocking(node.into(), ctxt)
                        .map(BorrowPcgEdgeLike::to_owned_edge),
                );
            }
        }
        delegations
    }

    /// Packs the expansions at or below `place` that can be packed without
    /// losing information.
    ///
    /// Under [`PackStrategy::Lazy`] this is the only point at which such
    /// expansions are packed: `place` is about to be required at a capability
    /// it cannot hold while it is expanded.
    pub(crate) fn pack_expansions_for_obtain_of(
        &mut self,
        place: Place<'tcx>,
    ) -> Result<(), PcgError> {
        // Packing an expansion can label lifetime projections, which changes
        // the edges that contain them, and can change capabilities. So each
        // expansion to pack is identified in the graph the previous packing
        // left.
        while let Some(edge) = self.packable_expansion_at_or_below(place) {
            self.remove_edge_and_perform_associated_state_updates(
                &edge,
                &format!(
                    "Pack expansions to obtain {}",
                    place.display_string(self.ctxt)
                ),
            )?;
        }
        Ok(())
    }

    fn packable_expansion_at_or_below(&self, place: Place<'tcx>) -> Option<BorrowPcgEdge<'tcx>> {
        let fg = self.pcg.borrow.graph.frozen_graph();
        fg.leaf_edges(self.ctxt)
            .into_iter()
            .find(|edge| {
                let BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) = edge.kind() else {
                    return false;
                };
                expansion
                    .base()
                    .as_current_place()
                    .is_some_and(|base| place.is_prefix_of(base))
                    && expansion.is_packable(self.pcg.place_capabilities, self.ctxt)
            })
            .map(BorrowPcgEdgeLike::to_owned_edge)
    }

    /// Mutable borrows, expansions of lifetime projections, assignments and
    /// loops can label a lifetime projection `rp` as a snapshot and add an edge
    /// from the snapshot to the future `rp`. The snapshot is *settled* once `rp`
    /// is current again and that edge is the snapshot's only use. A settled
    /// snapshot is merged into `rp`, so that repeated borrows of a place do not
    /// build up a chain of snapshots. The edges into the snapshot must hold
    /// under the same conditions as its edge into `rp`, so that they keep their
    /// conditions when they point to `rp`.
    fn merge_settled_snapshots(&mut self) -> Result<(), PcgError> {
        for (edge, snapshot) in self.settled_snapshots() {
            self.record_and_apply_action(
                BorrowPcgAction::remove_edge(edge, "Snapshot is settled").into(),
            )?;
            self.record_and_apply_action(
                BorrowPcgAction::remove_lifetime_projection_label(snapshot, "Snapshot is settled")
                    .into(),
            )?;
        }
        Ok(())
    }

    /// The settled snapshots, each with its edge into the current projection.
    /// Each such edge ends at an unlabelled projection, so merging one snapshot
    /// does not change another one's edge, and all of them can be merged in one
    /// pass. Merging a snapshot can settle a snapshot whose edge led into it;
    /// the next packing merges that one.
    fn settled_snapshots(&self) -> Vec<(BorrowPcgEdge<'tcx>, LocalLifetimeProjection<'tcx>)> {
        let ctxt = self.ctxt.bc_ctxt();
        let graph = &self.pcg.borrow.graph;
        let mut candidates: HashMap<
            PcgNode<'tcx>,
            (BorrowPcgEdge<'tcx>, LocalLifetimeProjection<'tcx>),
        > = graph
            .edges()
            .filter_map(|edge| {
                let BorrowPcgEdgeKind::BorrowFlow(flow) = edge.kind else {
                    return None;
                };
                let PlaceOrConst::Place(MaybeRemotePlace::Local(base)) = flow.long().base else {
                    return None;
                };
                let snapshot = flow.long().with_base(base);
                (flow.kind == BorrowFlowEdgeKind::Future(FutureEdgeKind::ToFutureSelf)
                    && matches!(snapshot.label(), Some(LifetimeProjectionLabel::Location(_)))
                    && snapshot.with_label(None, ctxt) == flow.short())
                .then(|| (snapshot.into(), (edge.to_owned_edge(), snapshot)))
            })
            .collect();
        if candidates.is_empty() {
            return Vec::new();
        }
        for edge in graph.edges() {
            for node in edge.kind.blocked_nodes(ctxt) {
                if candidates
                    .get(&node)
                    .is_some_and(|(own, _)| own.kind() != edge.kind)
                {
                    candidates.remove(&node);
                }
            }
            for node in edge.kind.blocked_by_nodes(ctxt) {
                let node = node.into();
                if candidates
                    .get(&node)
                    .is_some_and(|(own, _)| own.conditions() != edge.conditions)
                {
                    candidates.remove(&node);
                }
            }
        }
        candidates.into_values().collect()
    }

    /// Identifies the leaf edges to remove next: the deref edges to some place,
    /// or else one other edge.
    ///
    /// If `ancestor_place` is defined, we only consider a subset of the edges.
    ///
    /// The subset of edges is defined as follows:
    ///
    /// A node *can be killed* if it has a related current place that is a
    /// postfix of `ancestor_place`.
    ///
    /// Then we consider edges where either:
    ///
    /// 1. The edge is an expansion edge, and the base can be killed, or
    /// 2. The edge is some other kind of edge, and all of the blocking nodes can be killed
    fn identify_leaf_edges_to_remove<'slf>(
        &'slf self,
        ancestor_place: Option<Place<'tcx>>,
    ) -> Option<RemovalAction<'tcx>> {
        enum ShouldKillNode {
            Yes { reason: Cow<'static, str> },
            No,
        }

        let ctxt = self.ctxt;
        let location = self.location();

        let ancestor_predicate_allows_killing = |p: LocalNode<'tcx>| {
            let place = match p {
                PcgNode::Place(p) => p,
                PcgNode::LifetimeProjection(rp) => rp.base(),
            };
            if let Some(ancestor_place) = ancestor_place
                && (!place.is_current() || !ancestor_place.place().is_prefix_of(place.place()))
            {
                return false;
            }
            true
        };

        let should_kill_node = |p: LocalNode<'tcx>, fg: &FrozenGraphRef<'slf, 'tcx>| {
            let place = match p {
                PcgNode::Place(p) => p,
                PcgNode::LifetimeProjection(rp) => rp.base(),
            };
            if !ancestor_predicate_allows_killing(p) {
                return ShouldKillNode::No;
            }

            let has_live_rawptr_delegation = |node: PcgNode<'tcx>| {
                fg.get_edges_blocking(node, ctxt.bc_ctxt())
                    .into_iter()
                    .any(|e| {
                        matches!(
                            e.kind,
                            BorrowPcgEdgeKind::Delegation(delegation)
                                if !ctxt.bc().is_dead(
                                    delegation.rawptr_place.place().into(),
                                    location,
                                )
                        )
                    })
            };
            if has_live_rawptr_delegation(PcgNode::from(p))
                || (matches!(p, PcgNode::LifetimeProjection(_))
                    && has_live_rawptr_delegation(PcgNode::from(place)))
            {
                return ShouldKillNode::No;
            }

            if place.is_old() {
                return ShouldKillNode::Yes {
                    reason: "Place is old".into(),
                };
            }

            if p.is_place()
                && !place.place().projection.is_empty()
                && !fg.has_edge_blocking(place.into(), ctxt)
                && !place.place().contains_unsafe_deref(ctxt)
            {
                return ShouldKillNode::Yes {
                    reason:
                        "Node is a place with a non-empty projection and is not blocked by an edge"
                            .into(),
                };
            }
            if ctxt.bc().is_dead(p.into(), location) {
                return ShouldKillNode::Yes {
                    reason: "Borrow-checker reports node as dead".into(),
                };
            }

            ShouldKillNode::No
        };

        enum ShouldPackEdge {
            Yes { reason: Cow<'static, str> },
            No,
        }

        let fg = self.pcg.borrow.graph.frozen_graph();
        let location = self.location();
        let should_pack_edge = |edge: &BorrowPcgEdgeKind<'tcx>| {
            if let BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) = edge {
                if !ancestor_predicate_allows_killing(expansion.base()) {
                    return ShouldPackEdge::No;
                }
                if expansion.expansion().iter().all(|node| {
                    node.is_old() || self.ctxt.bc().is_dead(node.place().into(), location)
                }) {
                    ShouldPackEdge::Yes {
                        reason: "Expansion is old or dead".into(),
                    }
                } else if self.ctxt.settings().pack_strategy == PackStrategy::Eager
                    && expansion.is_packable(self.pcg.place_capabilities, self.ctxt)
                {
                    ShouldPackEdge::Yes {
                        reason: format!(
                            "Expansion {} is packable",
                            expansion.display_string(self.ctxt)
                        )
                        .into(),
                    }
                } else if let BorrowPcgExpansion::LifetimeProjection(lp_expansion) = expansion
                    && let base = lp_expansion.base.base()
                    && base.place().as_borrowed_place(self.ctxt).is_some()
                    && !fg.nodes(self.ctxt).contains(&PcgNode::Place(base))
                {
                    // Lifetime projection expansions are never packable, and
                    // their nodes stay live as long as the region. Once the
                    // borrowed place this one expands has left the graph, it
                    // is packed here; otherwise it would stay as a labelled
                    // snapshot of that place.
                    ShouldPackEdge::Yes {
                        reason: format!(
                            "Base place of {} is no longer in the graph",
                            expansion.display_string(self.ctxt)
                        )
                        .into(),
                    }
                } else {
                    ShouldPackEdge::No
                }
            } else {
                let mut why_killed_reasons = Vec::new();
                for node in edge.blocked_by_nodes(self.ctxt) {
                    if let ShouldKillNode::Yes { reason } = should_kill_node(node, &fg) {
                        why_killed_reasons.push(format!(
                            "{}: {}",
                            node.display_string(self.ctxt),
                            reason
                        ));
                    } else {
                        tracing::debug!(
                            "Node {} will not be killed",
                            node.display_string(self.ctxt)
                        );
                        return ShouldPackEdge::No;
                    }
                }
                ShouldPackEdge::Yes {
                    reason: format!(
                        "Edge is blocked by nodes that should be killed: {}",
                        why_killed_reasons.join(", ")
                    )
                    .into(),
                }
            }
        };
        let removal_reason = |edge: &BorrowPcgEdgeKind<'tcx>| {
            tracing::debug!("Checking leaf edge: {}", edge.display_string(self.ctxt));
            if let BorrowPcgEdgeKind::Delegation(delegation) = edge {
                match should_kill_node(delegation.rawptr_place.into(), &fg) {
                    ShouldKillNode::Yes { reason } => Some(reason),
                    ShouldKillNode::No => None,
                }
            } else {
                match should_pack_edge(edge) {
                    ShouldPackEdge::Yes { reason } => Some(reason),
                    ShouldPackEdge::No => None,
                }
            }
        };
        let leaf_edges = fg.leaf_edges(self.ctxt);
        let deref_edges = || {
            leaf_edges.iter().filter_map(|edge| match edge.kind {
                BorrowPcgEdgeKind::Deref(deref) => Some((edge, deref)),
                _ => None,
            })
        };
        // The removable deref edges to one place are removed together.
        if let Some((place, reason)) = deref_edges()
            .find_map(|(edge, deref)| Some((deref.deref_place, removal_reason(edge.kind)?)))
        {
            let edges = deref_edges()
                .filter(|(edge, deref)| {
                    deref.deref_place == place && removal_reason(edge.kind).is_some()
                })
                .map(|(edge, deref)| Conditioned::new(*deref, edge.conditions.clone()))
                .collect();
            return Some(RemovalAction::RemoveDerefEdgesTo(place, edges, reason));
        }
        leaf_edges.iter().find_map(|edge| {
            if matches!(edge.kind, BorrowPcgEdgeKind::Deref(_)) {
                return None;
            }
            let reason = removal_reason(edge.kind)?;
            Some(RemovalAction::RemoveOtherEdge(edge.to_owned_edge(), reason))
        })
    }
}
