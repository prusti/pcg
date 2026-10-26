#[cfg(feature = "visualization")]
use crate::visualization::stmt_graphs;
use crate::{
    HasSettings,
    action::{AppliedAction, BorrowPcgAction, OwnedPcgAction, PcgAction},
    borrow_pcg::{
        self,
        action::{ApplyActionResult, LabelPlaceReason},
        borrow_pcg_edge::BorrowPcgEdge,
        borrow_pcg_expansion::{BorrowPcgExpansion, PlaceExpansion},
        edge::{
            borrow_flow::private::FutureEdgeKind,
            deref::DerefEdge,
            kind::{BorrowPcgEdgeKind, BorrowPcgEdgeType},
        },
        edge_data::{EdgeData, LabelNodePredicate},
        graph::Conditioned,
        state::{BorrowStateMutRef, BorrowsStateLike},
    },
    owned_pcg::{LocalExpansions, RepackOp},
    pcg::{
        CapabilityKind, EvalStmtPhase, PcgNode, PcgNodeLike, PcgRef, PcgRefLike,
        obtain::{
            ActionApplier, HasSnapshotLocation, ObtainType, PlaceCollapser, PlaceObtainer,
            RenderDebugGraph, expand::PlaceExpander,
        },
        place_capabilities::{
            BlockType, PlaceCapabilities, PlaceCapabilitiesInterface, PlaceCapabilitiesReader,
        },
        visitor::upgrade::AdjustCapabilityReason,
    },
    pcg_validity_assert,
    rustc_interface::middle::mir,
    utils::{
        CompilerCtxt, DataflowCtxt, DebugCtxt, HasBorrowCheckerCtxt, HasPlace, PackStrategy,
        data_structures::HashSet, display::DisplayWithCompilerCtxt, maybe_old::MaybeLabelledPlace,
    },
};
use std::cmp::Ordering;

use crate::utils::{Place, SnapshotLocation};

use super::{PcgError, PcgVisitor};
impl<'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PcgVisitor<'_, 'a, 'tcx, Ctxt> {
    pub(crate) fn place_obtainer(&mut self) -> PlaceObtainer<'_, 'a, 'tcx, Ctxt> {
        let prev_snapshot_location = self.prev_snapshot_location();
        let pcg_ref = self.pcg.into();
        PlaceObtainer::new(
            pcg_ref,
            Some(&mut self.actions),
            self.ctxt,
            self.analysis_location.location,
            prev_snapshot_location,
        )
    }
    pub(crate) fn record_and_apply_action(
        &mut self,
        action: PcgAction<'tcx>,
    ) -> Result<(), PcgError> {
        self.place_obtainer().record_and_apply_action(action)
    }
}

impl<'state, 'a: 'state, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PlaceCollapser<'a, 'tcx>
    for PlaceObtainer<'state, 'a, 'tcx, Ctxt>
{
    fn get_local_expansions(&self, local: mir::Local) -> &LocalExpansions<'tcx> {
        self.pcg.owned[local].expansions()
    }

    fn borrows_state(&mut self) -> BorrowStateMutRef<'_, 'tcx> {
        self.pcg.borrow.as_mut_ref()
    }

    fn capabilities(&mut self) -> &mut PlaceCapabilities<'tcx> {
        self.pcg.place_capabilities
    }

    fn leaf_places(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> HashSet<Place<'tcx>> {
        let owned_places = self.blocked_owned_places(ctxt);
        let mut leaf_places: HashSet<Place<'tcx>> = self
            .pcg
            .owned
            .leaf_places(ctxt)
            .into_iter()
            .map(Into::into)
            .filter(|p| !owned_places.contains(p))
            .collect();
        leaf_places.extend(
            self.pcg
                .borrow
                .graph
                .frozen_graph()
                .leaf_nodes(ctxt)
                .iter()
                .filter_map(|node| node.as_current_place()),
        );
        leaf_places
    }

    fn blocked_owned_places(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> HashSet<Place<'tcx>> {
        self.pcg.borrow.graph().owned_places(ctxt)
    }
}

impl<'state, 'a: 'state, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>>
    PlaceObtainer<'state, 'a, 'tcx, Ctxt>
{
    /// The capability that `place` has once nothing blocks it.
    fn unblocked_capability(&self, place: Place<'tcx>) -> CapabilityKind {
        // TODO: If the place projects a shared ref, do we even need to restore a capability?
        //
        // For owned places we consult the initialisation state so we
        // don't unsoundly restore to `Exclusive` when the place was
        // moved out on some incoming path (#137): the join of the init
        // trees would then leave the place as `Uninit`, which maps to
        // `Write`.
        if place.place().projects_shared_ref(self.ctxt)
            || self
                .ctxt
                .body_analysis()
                .is_read_only_in_loop(self.location().block, place)
        {
            CapabilityKind::Read
        } else if let Some(owned) = place.as_owned_place(self.ctxt)
            && let Some(init_cap) = self.pcg.owned.owned_capability(owned)
        {
            init_cap
        } else {
            CapabilityKind::Exclusive
        }
    }

    /// The capability that `place` gets back when the edge blocking it is
    /// removed: it was lent (no capability), packed (no capability), or a
    /// mutable reference whose dereference is packed (`e`).
    fn regained_capability(&self, place: Place<'tcx>) -> Option<CapabilityKind> {
        // The place could come from a local that was conditionally allocated
        // and therefore we can't get back to it, and certainly shouldn't give
        // it any capability
        // TODO: Perhaps the join should label such places?
        if !self.pcg.owned.is_allocated(place.local) {
            return None;
        }
        let blocked_cap = self.pcg.capability_of(place, self.ctxt);
        let unblocked_cap = self.unblocked_capability(place);
        (matches!(
            blocked_cap,
            None | Some(CapabilityKind::Write | CapabilityKind::ShallowExclusive)
        ) && blocked_cap != Some(unblocked_cap))
        .then_some(unblocked_cap)
    }

    /// Updates `place` after the edge blocking it was removed: a frozen leaf
    /// is unfrozen, and the placeholder labels of its lifetime projections
    /// are removed.
    fn place_unblocked(&mut self, place: Place<'tcx>, context: &str) -> Result<(), PcgError> {
        if !self.pcg.owned.is_allocated(place.local) {
            return Ok(());
        }
        if self
            .pcg
            .place_capability_equals(place, CapabilityKind::Read, self.ctxt)
            && self.unblocked_capability(place) == CapabilityKind::Exclusive
            && self.frozen_ancestor(place) == place
            && self
                .pcg
                .place_capabilities
                .capabilities_for_strict_postfixes_of(place)
                .next()
                .is_none()
        {
            self.record_and_apply_action(
                BorrowPcgAction::unfreeze(place, context.to_owned()).into(),
            )?;
        }
        for rp in place.lifetime_projections(self.ctxt) {
            self.record_and_apply_action(
                    BorrowPcgAction::remove_lifetime_projection_label(
                        rp.with_placeholder_label(self.ctxt).into(),
                        format!(
                            "Place {} unblocked: remove placeholder label of rps of newly unblocked nodes",
                            place.display_string(self.ctxt.bc_ctxt())
                        ),
                    )
                    .into(),
                )?;
        }
        Ok(())
    }
    /// The places blocked by `edge` that, after its removal, are no longer
    /// blocked and are still tracked.
    fn places_unblocked_by_removal(&self, edge: &BorrowPcgEdgeKind<'tcx>) -> Vec<Place<'tcx>> {
        let borrow_places = self.pcg.borrow.graph.places(self.ctxt.bc_ctxt());
        let fg = self.pcg.borrow.graph.frozen_graph();
        edge.blocked_nodes(self.ctxt.bc_ctxt())
            .filter(|node| !fg.has_edge_blocking(*node, self.ctxt.bc_ctxt()))
            .filter_map(|node| node.as_current_place())
            // Only places that are still tracked somewhere. After a loop
            // abstraction edge is removed, the blocked place (e.g.
            // `(*variant).fields`) may no longer appear in either the owned
            // PCG or the borrow graph; giving a capability there would
            // violate the invariant that every capability-holding place must
            // be tracked.
            .filter(|place| {
                borrow_places.contains(place)
                    || self.pcg.owned.contains_place(*place, self.ctxt.bc_ctxt())
            })
            .collect()
    }

    /// If the following conditions apply:
    /// 1. `expansion` is a dereference of a place `p`
    /// 2. `*p` does not contain any borrows
    /// 3. The target of this expansion is not labelled
    ///
    /// Then we perform an optimization where instead of connecting the blocked
    /// lifetime projection to the current one, we instead remove the label of
    /// the blocked lifetime projection.
    ///
    /// This is sound because the lifetime projection only contains the single
    /// borrow that `p` refers to and therefore the set of borrows cannot be
    /// changed. In other words, the set of borrows in the lifetime projection
    /// at the point it was dereferenced is the same as the current set of
    /// borrows in the lifetime projection.
    ///
    /// Note the third condition: if the expansion is labelled, that indicates
    /// that the expansion occurred at a point where `p` had a different value
    /// than the current one. We don't want to perform this optimization because
    /// the it is referring to this different value.
    /// For test case see rustls-pki-types@1.11.0 `server_name::parser::Parser::`<'`a>::read_char`
    ///
    /// TODO: In the above test case, should the parent place also be labelled?
    fn unlabel_blocked_region_projections_if_applicable(
        &mut self,
        deref: &DerefEdge<'tcx>,
        context: &str,
    ) -> Result<(), PcgError> {
        if deref.deref_place.is_current()
            && deref.deref_place.lifetime_projections(self.ctxt).is_empty()
        {
            self.unlabel_source_lifetime_projections(deref, context)
        } else {
            Ok(())
        }
    }

    pub(crate) fn remove_deref_edges_to(
        &mut self,
        deref_place: MaybeLabelledPlace<'tcx>,
        edges: HashSet<Conditioned<DerefEdge<'tcx>>>,
        context: &str,
    ) -> Result<(), PcgError> {
        let ref_place = deref_place
            .as_current_place()
            .map(|deref_place| deref_place.parent_place().unwrap());
        let edges = edges.into_iter().collect::<Vec<_>>();
        let mut unblocked = vec![];
        for (i, edge) in edges.iter().enumerate() {
            let borrow_edge: BorrowPcgEdge<'tcx> =
                BorrowPcgEdge::new(edge.value.into(), edge.conditions.clone());
            // Removing the last edge packs the dereference into the reference.
            unblocked = self.remove_edge_regaining(borrow_edge, context.to_owned(), |slf| {
                // Perhaps the place isn't yet a leaf(e.g. the ref itself is
                // conditionally borrowed): then it stays without its
                // capability
                ref_place
                    .filter(|ref_place| {
                        i + 1 == edges.len() && slf.pcg.is_leaf_place(*ref_place, slf.ctxt)
                    })
                    .into_iter()
                    .collect()
            })?;
            self.unlabel_blocked_region_projections_if_applicable(&edge.value, context)?;
        }
        if let Some(deref_place) = deref_place.as_current_place() {
            self.apply_action(
                BorrowPcgAction::label_place_and_update_related_capabilities(
                    deref_place,
                    self.prev_snapshot_location(),
                    LabelPlaceReason::Collapse,
                )
                .into(),
            )?;
        }
        for place in unblocked {
            self.place_unblocked(place, &format!("{context}: remove_deref_edges_to"))?;
        }
        Ok(())
    }

    #[tracing::instrument(skip(self, edge))]
    pub(crate) fn remove_edge_and_perform_associated_state_updates(
        &mut self,
        edge: &BorrowPcgEdge<'tcx>,
        context: &str,
    ) -> Result<(), PcgError> {
        if let BorrowPcgEdgeKind::Deref(deref) = edge.kind() {
            return self.remove_deref_edges_to(
                deref.deref_place,
                vec![Conditioned::new(*deref, edge.conditions.clone())]
                    .into_iter()
                    .collect(),
                context,
            );
        }
        // This is true iff the expansion is for a place (not a region projection), and changes
        // could have been made to the root place via the expansion
        // We check that the base is place and either:
        // - The base has no capability, meaning it was previously expanded mutably
        // - The base has write capability, it is a mutable ref
        let is_mutable_place_expansion = if let BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) =
            edge.kind()
            && let Some(place) = expansion.base().as_current_place()
        {
            matches!(
                self.pcg.capability_of(place, self.ctxt),
                Some(CapabilityKind::Write) | None
            )
        } else {
            false
        };

        // After removing an edge, some nodes may become accessible: an
        // unpacking is packed, or a loan ends.
        let unblocked = self.remove_edge_regaining(edge.clone(), context.to_owned(), |slf| {
            slf.places_unblocked_by_removal(&edge.value)
        })?;
        for place in unblocked {
            self.place_unblocked(place, context)?;
        }

        match &edge.value {
            BorrowPcgEdgeKind::Deref(deref) => {
                self.unlabel_blocked_region_projections_if_applicable(deref, context)?;
                if deref.deref_place.is_current() {
                    self.apply_action(
                        BorrowPcgAction::label_place_and_update_related_capabilities(
                            deref.deref_place.place(),
                            self.prev_snapshot_location(),
                            LabelPlaceReason::Collapse,
                        )
                        .into(),
                    )?;
                }
            }
            BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) => {
                if is_mutable_place_expansion {
                    // If the expansion contained region projections, we need to
                    // label them, they will flow into the now unblocked
                    // projection (i.e. the one obtained by removing the
                    // placeholder label)

                    // For example, if we a are packing *s.i into *s at l
                    // we need to label *s.i|'s to  *s|'s at l
                    // because we will remove the label from *s|'s at l'
                    // to become *s|'s. Otherwise we'd have both *s|'s and *s.i|'s
                    for exp_node in expansion.expansion() {
                        if let PcgNode::Place(place) = exp_node {
                            for rp in place.lifetime_projections(self.ctxt) {
                                tracing::debug!(
                                    "labeling region projection: {}",
                                    rp.display_string(self.ctxt)
                                );
                                self.record_and_apply_action(
                                    BorrowPcgAction::label_lifetime_projection(
                                        LabelNodePredicate::equals_lifetime_projection(rp),
                                        Some(self.prev_snapshot_location().into()),
                                        format!(
                                            "{}: {}",
                                            context, "Label region projections of expansion"
                                        ),
                                    )
                                    .into(),
                                )?;
                            }
                        }
                    }
                }
            }
            BorrowPcgEdgeKind::Borrow(borrow) => {
                if self.ctxt.bc().is_dead(
                    borrow
                        .assigned_lifetime_projection(self.ctxt)
                        .to_pcg_node(self.ctxt.bc_ctxt()),
                    self.location(),
                ) && let MaybeLabelledPlace::Current(place) = borrow.assigned_ref()
                    && let Some(existing_cap) = self.pcg.capability_of(place, self.ctxt)
                {
                    self.record_and_apply_action(
                        BorrowPcgAction::weaken(
                            place,
                            existing_cap,
                            Some(CapabilityKind::Write),
                            "remove borrow edge",
                        )
                        .into(),
                    )?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// As an optimization, for expansions of the form {y, y|'y at l} -> *y,
    /// if *y doesn't contain any borrows, we currently don't introduce placeholder
    /// projections for y|'y: the set of borrows is guaranteed not to change as long as *y
    /// is in the graph.
    ///
    /// Accordingly, when we want to remove *y in such cases, we just remove the
    /// label rather than use the normal logic (of renaming the placeholder
    /// projection to the current one).
    fn unlabel_source_lifetime_projections(
        &mut self,
        deref: &DerefEdge<'tcx>,
        context: &str,
    ) -> Result<(), PcgError> {
        self.record_and_apply_action(
            BorrowPcgAction::remove_lifetime_projection_label(
                deref.blocked_lifetime_projection,
                format!("{context}: unlabel blocked_region_projections"),
            )
            .into(),
        )?;
        Ok(())
    }

    /// Returns the read copies in the unpacking of `place` to it, for an
    /// unpacking that cannot be packed (because places in it are borrowed).
    /// Borrowed copies cannot be returned and are kept.
    pub(crate) fn drop_read_copies(&mut self, place: Place<'tcx>) -> Result<(), PcgError> {
        let copies = self
            .pcg
            .place_capabilities
            .capabilities_for_strict_postfixes_of(place)
            .collect::<Vec<_>>();
        let borrowed = copies
            .iter()
            .map(|(p, _)| *p)
            .filter(|p| self.holds_freeze(*p))
            .collect::<Vec<_>>();
        let ctxt = self.ctxt;
        for (p, cap) in copies {
            if borrowed.iter().any(|b| b.is_prefix_of(p)) {
                continue;
            }
            pcg_validity_assert!(
                cap.is_read(),
                [ctxt],
                "{} in the read unpacking of {} has capability {:?}",
                p.display_string(self.ctxt),
                place.display_string(self.ctxt),
                cap
            );
            self.record_and_apply_action(
                BorrowPcgAction::weaken(p, cap, None, "return read copy").into(),
            )?;
        }
        Ok(())
    }

    pub(crate) fn upgrade_read_to_exclusive(&mut self, place: Place<'tcx>) -> Result<(), PcgError> {
        tracing::debug!(
            "upgrade_read_to_exclusive: {}",
            place.display_string(self.ctxt.bc_ctxt())
        );
        self.drop_read_copies(place)?;
        let frozen = self.frozen_ancestor(place);
        self.end_freeze(frozen, AdjustCapabilityReason::UpgradeReadToExclusive)?;
        if frozen != place {
            self.label_rps_up_to(
                place.parent_place().unwrap(),
                frozen,
                AdjustCapabilityReason::UpgradeReadToExclusive,
            )?;
        }
        Ok(())
    }

    // This function is called if we want to obtain non-read capability to `place`
    // If the closest ancestor of `place` has read capability, then we are allowed to
    // upgrade the capability of the ancestor to `E` in exchange for downgrading all
    // other pre / postfix places to None.
    //
    // This is sound because if we need to obtain non-read capability to
    // `place`, and there are any ancestors of `place` in the graph with R
    // capability, one such ancestor originally had E capability was
    // subsequently downgraded. This function finds such an ancestor (if one
    // exists), and performs the capability exchange.
    pub(crate) fn upgrade_closest_read_ancestor_to_exclusive_and_update_rps(
        &mut self,
        place: Place<'tcx>,
    ) -> Result<(), PcgError> {
        let mut expand_root = place;
        loop {
            if let Some(cap) = self.pcg.capability_of(expand_root, self.ctxt) {
                if cap.is_read() {
                    self.upgrade_read_to_exclusive(expand_root)?;
                }
                return Ok(());
            }
            if let Some(parent) = expand_root.parent_place() {
                expand_root = parent;
            } else {
                return Ok(());
            }
        }
    }

    pub(crate) fn record_and_apply_action(
        &mut self,
        action: PcgAction<'tcx>,
    ) -> Result<(), PcgError>
    where
        Ctxt: HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>,
    {
        let result = self.apply_action_without_recording(&action)?;
        self.record_applied_action(action, result);
        Ok(())
    }

    /// Removes `edge`; the places `unblocked` finds unblocked afterwards get
    /// their capability back as part of the removal. Returns those places.
    pub(crate) fn remove_edge_regaining(
        &mut self,
        edge: BorrowPcgEdge<'tcx>,
        context: String,
        unblocked: impl FnOnce(&Self) -> Vec<Place<'tcx>>,
    ) -> Result<Vec<Place<'tcx>>, PcgError> {
        let result = self.apply_action_without_recording(
            &BorrowPcgAction::remove_edge(edge.clone(), context.clone()).into(),
        )?;
        let unblocked = unblocked(self);
        let regained = unblocked
            .iter()
            .filter_map(|place| {
                self.regained_capability(*place)
                    .map(|capability| (*place, capability))
            })
            .collect::<Vec<_>>();
        let action = BorrowPcgAction::remove_edge_regaining(edge, regained, context).into();
        // The edge is already removed, this only gives back the capabilities.
        self.apply_action_without_recording(&action)?;
        self.record_applied_action(action, result);
        Ok(unblocked)
    }

    fn apply_action_without_recording(
        &mut self,
        action: &PcgAction<'tcx>,
    ) -> Result<ApplyActionResult, PcgError> {
        tracing::debug!("Applying Action: {}", action.debug_line(self.ctxt));
        Ok(match action {
            PcgAction::Borrow(action) => {
                self.pcg
                    .borrow
                    .apply_action(action.clone(), self.pcg.place_capabilities, self.ctxt)
            }
            PcgAction::Owned(owned_action) => match owned_action.kind {
                RepackOp::Expand(expand) => {
                    self.pcg.owned.perform_expand_action(
                        expand,
                        self.pcg.place_capabilities,
                        self.ctxt,
                    );
                    ApplyActionResult::changed_no_display()
                }
                RepackOp::DerefShallowInit(from, to) => {
                    let target_places = from.expand_one_level(to, self.ctxt)?.expansion();
                    let capability_projections = self.pcg.owned[from.local].expansions_mut();
                    capability_projections.insert_expansion(
                        from,
                        PlaceExpansion::from_places(target_places.clone(), self.ctxt),
                    );
                    for target_place in target_places {
                        self.pcg.place_capabilities.insert(
                            target_place,
                            CapabilityKind::Read,
                            self.ctxt,
                        );
                    }
                    ApplyActionResult::changed_no_display()
                }
                RepackOp::Collapse(collapse) => {
                    let capability_projections = self.pcg.owned[collapse.local()].expansions_mut();
                    capability_projections.perform_collapse_action(
                        collapse,
                        self.pcg.place_capabilities,
                        self.ctxt,
                    );
                    ApplyActionResult::changed_no_display()
                }
                RepackOp::Weaken(weaken) => {
                    pcg_validity_assert!(
                        self.pcg
                            .place_capability_equals(weaken.place, weaken.from, self.ctxt)
                            || weaken.place.contains_unsafe_deref(self.ctxt)
                    );
                    self.pcg
                        .place_capabilities
                        .insert(weaken.place, weaken.to, self.ctxt);
                    ApplyActionResult::changed_no_display()
                }
                _ => unreachable!(),
            },
        })
    }

    fn record_applied_action(&mut self, action: PcgAction<'tcx>, result: ApplyActionResult) {
        #[cfg(feature = "visualization")]
        let location = self.location();
        #[cfg(feature = "visualization")]
        let phase = self.phase();
        if let Some(actions) = &mut self.actions {
            #[cfg(feature = "visualization")]
            if let Some(analysis_ctxt) = self.ctxt.try_into_analysis_ctxt()
                && let Some(phase) = phase
            {
                let pcg_ref = PcgRef {
                    borrow: self.pcg.borrow.as_ref(),
                    place_capabilities: self.pcg.place_capabilities,
                    owned: self.pcg.owned,
                };
                analysis_ctxt.generate_pcg_debug_visualization_graph(
                    location,
                    stmt_graphs::ToGraph::Action(phase, actions.len()),
                    pcg_ref,
                );
            }
            actions.push(AppliedAction::new(action, result));
        }
    }
    pub(crate) fn phase(&self) -> Option<EvalStmtPhase> {
        match self.prev_snapshot_location {
            SnapshotLocation::Before(analysis_location) => Some(analysis_location.eval_stmt_phase),
            _ => None,
        }
    }
}

impl<'state, 'a: 'state, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx> + DebugCtxt> ActionApplier<'tcx>
    for PlaceObtainer<'state, 'a, 'tcx, Ctxt>
{
    fn apply_action(&mut self, action: PcgAction<'tcx>) -> Result<(), PcgError> {
        self.record_and_apply_action(action)
    }
}

/// Whether the place must be collapsed before it can hold `obtain_cap`.
fn requires_collapse(current_cap: Option<CapabilityKind>, obtain_cap: CapabilityKind) -> bool {
    current_cap
        .is_none_or(|cap| matches!(cap.partial_cmp(&obtain_cap), Some(Ordering::Less) | None))
}

impl<'state, 'a: 'state, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>>
    PlaceObtainer<'state, 'a, 'tcx, Ctxt>
{
    /// Ensures that the place is expanded to the given place, with a certain
    /// capability.
    ///
    /// This also handles corresponding lifetime projections of the place.
    #[tracing::instrument(skip(self))]
    pub(crate) fn obtain(
        &mut self,
        place: Place<'tcx>,
        obtain_type: ObtainType,
    ) -> Result<(), PcgError> {
        let obtain_cap = obtain_type.capability(place, self.ctxt);

        // Under `PackStrategy::Lazy` the expansions below `place` were not
        // packed as soon as they became packable, so they are packed here,
        // where a capability that `place` cannot hold while it is expanded is
        // about to be required.
        if self.ctxt.settings().pack_strategy == PackStrategy::Lazy
            && requires_collapse(self.pcg.capability_of(place, self.ctxt), obtain_cap)
        {
            self.pack_expansions_for_obtain_of(place)?;
        }

        if obtain_cap.is_write() {
            tracing::debug!(
                "labeling and removing capabilities for deref projections of postfix places"
            );
            self.record_and_apply_action(
                BorrowPcgAction::label_place_and_update_related_capabilities(
                    place,
                    self.prev_snapshot_location(),
                    LabelPlaceReason::Write,
                )
                .into(),
            )?;
            self.record_and_apply_action(
                BorrowPcgAction::label_lifetime_projection(
                    LabelNodePredicate::And(vec![
                        LabelNodePredicate::PlaceEquals(place),
                        LabelNodePredicate::InSourceNodes,
                        LabelNodePredicate::EdgeType(BorrowPcgEdgeType::BorrowFlow {
                            future_edge_kind: Some(FutureEdgeKind::FromExpansion),
                        }),
                    ]),
                    None,
                    "label place and update related capabilities",
                )
                .into(),
            )?;
            self.render_debug_graph(None, "after step 1");
        }

        let current_cap = self.pcg.capability_of(place, self.ctxt);
        tracing::debug!(
            "Obtain {:?} to place {} in phase {:?}: Current cap: {:?}, Obtain cap: {:?}",
            obtain_type,
            place.display_string(self.ctxt.bc_ctxt()),
            self.phase(),
            current_cap,
            obtain_cap
        );

        // STEP 2
        if requires_collapse(current_cap, obtain_cap) {
            // If we want to get e.g. write permission but we currently have
            // read permission, we will obtain read with the collapse and then
            // upgrade in the subsequent step
            let collapse_cap = if current_cap == Some(CapabilityKind::Read) {
                CapabilityKind::Read
            } else {
                obtain_cap
            };
            // When collapsing to write capability (an overwrite or a
            // StorageDead of e.g. a partially-moved local), leaves that still
            // hold exclusive capability must be explicitly weakened first, so
            // that consumers see the capability drop; see
            // <https://github.com/prusti/pcg/issues/137>.
            if collapse_cap.is_write() {
                let to_weaken = self
                    .pcg
                    .place_capabilities
                    .owned_capabilities(place.local, self.ctxt)
                    .filter_map(|(p, k)| {
                        (place.is_prefix_of(p) && (k.is_exclusive() || k.is_shallow_exclusive()))
                            .then_some((p, *k))
                    })
                    .collect::<Vec<_>>();
                for (p, from_cap) in to_weaken {
                    let weaken = if obtain_type == ObtainType::ForStorageDead {
                        RepackOp::weaken_for_storage_dead(p, from_cap, CapabilityKind::Write)
                    } else {
                        RepackOp::weaken(p, from_cap, CapabilityKind::Write)
                    };
                    self.record_and_apply_action(PcgAction::Owned(OwnedPcgAction::new(
                        weaken, None,
                    )))?;
                }
            }
            tracing::debug!(
                "Collapsing owned places to {}",
                place.display_string(self.ctxt.bc_ctxt())
            );
            self.collapse_owned_places_and_lifetime_projections_to(
                place,
                collapse_cap,
                format!("Obtain {}", place.display_string(self.ctxt.bc_ctxt())),
                self.ctxt,
            )?;
            self.render_debug_graph(
                None,
                &format!(
                    "after step 2 (collapse owned places and lifetime projections to {})",
                    place.display_string(self.ctxt.bc_ctxt())
                ),
            );
        }

        // An unpacked borrowed place is read by freezing its unpacking (owned
        // places are frozen by the collapse above).
        if obtain_cap.is_read()
            && place.as_owned_place(self.ctxt).is_none()
            && self.pcg.capability_of(place, self.ctxt).is_none()
            && self
                .pcg
                .place_capabilities
                .capabilities_for_strict_postfixes_of(place)
                .next()
                .is_some()
        {
            self.record_and_apply_action(
                BorrowPcgAction::freeze(place, "read an unpacked place").into(),
            )?;
        }

        // STEP 3
        if !obtain_cap.is_read() {
            tracing::debug!(
                "Obtain {:?} to place {} in phase {:?}",
                obtain_type,
                place.display_string(self.ctxt.bc_ctxt()),
                self.phase()
            );
            // It's possible that we want to obtain exclusive or write permission to
            // a field that we currently only have read access for. For example,
            // consider the following case:
            //
            // There is an existing shared borrow of (*c).f1
            // Therefore we have read permission to *c, (*c).f1, and (*c).f2
            // Then, we want to create a mutable borrow of (*c).f2
            // This requires obtaining exclusive permission to (*c).f2
            //
            // We can upgrade capability of (*c).f2 from R to E by downgrading
            // all other pre-and postfix places of (*c).f2 (in this case c will
            // be downgraded to W and *c to None). In the example, (*c).f2 is
            // actually the closest read ancestor, but this is not always the
            // case (e.g. if we wanted to obtain (*c).f2.f3 instead)
            //
            // This also labels rps and adds placeholder projections
            self.upgrade_closest_read_ancestor_to_exclusive_and_update_rps(place)?;
            self.render_debug_graph(None, "after step 3");
        }

        // STEP 4
        if obtain_cap.is_write() {
            // If this place is a reference or contains references, reborrows of
            // (postfixes of) place may have not yet expired, and therefore the borrowed
            // caps are still in the PCG.
            // This will remove them (since we're going to overwrite anyways)
            self.pcg
                .place_capabilities
                .remove_all_strict_postfixes(place, self.ctxt);
            self.render_debug_graph(None, "after step 4");
        }

        self.expand_to(place, obtain_type, self.ctxt)?;

        if obtain_type == ObtainType::ForStorageDead
            && let Some(cap @ (CapabilityKind::Exclusive | CapabilityKind::ShallowExclusive)) =
                self.pcg.capability_of(place, self.ctxt)
        {
            // Temporary: mark as for_storage_dead until
            // https://github.com/prusti/pcg/issues/137 is resolved.
            self.record_and_apply_action(PcgAction::Owned(OwnedPcgAction::new(
                RepackOp::weaken_for_storage_dead(place, cap, CapabilityKind::Write),
                None,
            )))?;
        }

        self.render_debug_graph(None, "after step 5");

        Ok(())
    }
}

impl<'pcg, 'a: 'pcg, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PlaceExpander<'a, 'tcx>
    for PlaceObtainer<'pcg, 'a, 'tcx, Ctxt>
{
    fn contains_owned_expansion_to(&self, target: Place<'tcx>) -> bool {
        self.pcg.owned[target.local]
            .expansions()
            .contains_expansion_to(target, self.ctxt)
    }

    fn borrows_graph(&self) -> &borrow_pcg::graph::BorrowsGraph<'tcx> {
        self.pcg.borrow.graph
    }

    fn path_conditions(&self) -> borrow_pcg::validity_conditions::ValidityConditions {
        self.pcg.borrow.validity_conditions.clone()
    }

    fn update_capabilities_for_borrow_expansion(
        &mut self,
        expansion: &BorrowPcgExpansion<'tcx>,
        block_type: BlockType,
        _ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.pcg
            .place_capabilities
            .update_for_expansion(expansion, block_type, self.ctxt)
    }

    fn location(&self) -> mir::Location {
        self.location
    }

    fn update_capabilities_for_deref(
        &mut self,
        ref_place: Place<'tcx>,
        capability: CapabilityKind,
        _ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.pcg
            .place_capabilities
            .update_for_deref(ref_place, capability, self.ctxt)
    }

    fn freeze_for_read_unpacking(&mut self, base: Place<'tcx>) -> Result<(), PcgError> {
        if self
            .pcg
            .place_capability_equals(base, CapabilityKind::Exclusive, self.ctxt)
        {
            self.record_and_apply_action(BorrowPcgAction::freeze(base, "unpack for read").into())?;
        }
        Ok(())
    }

    fn capability_for_expand(
        &self,
        base_place: Place<'tcx>,
        obtain_type: ObtainType,
        ctxt: impl crate::utils::HasCompilerCtxt<'a, 'tcx>,
    ) -> CapabilityKind {
        let current_cap = if let Some(owned) = base_place.as_owned_place(ctxt) {
            self.pcg.owned.owned_capability(owned).unwrap()
        } else {
            self.pcg.place_capabilities.get(base_place, ctxt).unwrap()
        };
        obtain_type.capability_for_expand(base_place, current_cap, ctxt)
    }
}
