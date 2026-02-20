use crate::{
    Weaken,
    action::{AppliedAction, BorrowPcgAction, OwnedPcgAction, PcgAction},
    borrow_pcg::{
        action::{ApplyActionResult, LabelPlaceReason},
        borrow_pcg_edge::BorrowPcgEdge,
        borrow_pcg_expansion::{BorrowPcgPlaceExpansion, PlaceExpansion},
        edge::{
            borrow_flow::private::FutureEdgeKind,
            deref::DerefEdge,
            kind::{BorrowPcgEdgeKind, BorrowPcgEdgeType},
        },
        edge_data::{EdgeData, LabelNodePredicate},
        graph::Conditioned,
        state::{BorrowStateMutRef, BorrowsStateLike},
    },
    owned_pcg::RepackOp,
    pcg::{
        CapabilityKind, CapabilityLike, EvalStmtPhase, PcgNode, PcgNodeLike, PcgRef, PcgRefLike, PositiveCapability, SymbolicCapability, edge::EdgeMutability, obtain::{
            ActionApplier, HasSnapshotLocation, ObtainType, PlaceCollapser, PlaceObtainer,
            RenderDebugGraph, expand::PlaceExpander,
        }, place_capabilities::{BlockType, PlaceCapabilitiesReader}, visitor::upgrade::AdjustCapabilityReason
    },
    pcg_validity_assert,
    rustc_interface::middle::mir,
    utils::{
        CompilerCtxt, DataflowCtxt, DebugCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, HasPlace,
        data_structures::HashSet, display::DisplayWithCtxt, maybe_old::MaybeLabelledPlace,
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
    ) -> Result<(), PcgError<'tcx>> {
        self.place_obtainer().record_and_apply_action(action)
    }
}

impl<'state, 'a: 'state, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PlaceCollapser<'a, 'tcx>
    for PlaceObtainer<'state, 'a, 'tcx, Ctxt>
{
    fn get_local_expansions(&self, local: mir::Local) -> &crate::owned_pcg::LocalExpansions<'tcx> {
        self.pcg.owned[local].get_allocated()
    }

    fn borrows_state(&mut self) -> BorrowStateMutRef<'_, 'tcx> {
        self.pcg.borrow.as_mut_ref()
    }

    fn leaf_places(
        &self,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> crate::utils::data_structures::HashSet<Place<'tcx>> {
        let mut leaf_places = self.pcg.owned.leaf_places(ctxt);
        leaf_places.retain(|p| !self.pcg.borrow.graph().owned_places(ctxt).contains(p));
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
}

impl<'state, 'a: 'state, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>>
    PlaceObtainer<'state, 'a, 'tcx, Ctxt>
{
    fn restore_place(&mut self, place: Place<'tcx>, context: &str) -> Result<(), PcgError<'tcx>> {
        // The place to restore could come from a local that was conditionally
        // allocated and therefore we can't get back to it, and certainly
        // shouldn't give it any capability
        // TODO: Perhaps the join should label such places?
        if !self.pcg.owned.is_allocated(place.local) {
            return Ok(());
        }
        let blocked_cap = self.pcg.as_ref().get(place, self.ctxt).into_positive();

        // TODO: If the place projects a shared ref, do we even need to restore a capability?
        let restore_cap = if place.place().projects_shared_ref(self.ctxt) {
            PositiveCapability::Read
        } else {
            PositiveCapability::Exclusive
        };

        // The blocked capability would be None if the place was mutably
        // borrowed The capability would be Write if the place is a
        // mutable reference (when dereferencing a mutable ref, the ref
        // place retains write capability)
        if blocked_cap.is_none() || matches!(blocked_cap, Some(CapabilityKind::Write)) {
            self.record_and_apply_action(PcgAction::restore_capability(
                place,
                restore_cap,
                context.to_owned(),
                self.ctxt,
            ))?;
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
    fn update_unblocked_node_capabilities_and_remove_placeholder_projections(
        &mut self,
        edge: &BorrowPcgEdgeKind<'tcx>,
    ) -> Result<(), PcgError<'tcx>> {
        let fg = self.pcg.borrow.graph.frozen_graph();
        let blocked_nodes = edge.blocked_nodes(self.ctxt.bc_ctxt());

        // After removing an edge, some nodes may become accessible, their capabilities should be restored
        let to_restore = blocked_nodes
            .into_iter()
            .filter(|node| !fg.has_edge_blocking(*node, self.ctxt.bc_ctxt()))
            .collect::<Vec<_>>();

        for node in to_restore {
            if let Some(place) = node.as_current_place() {
                self.restore_place(
                    place,
                    "update_unblocked_node_capabilities_and_remove_placeholder_projections",
                )?;
            }
        }
        Ok(())
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
    ) -> Result<(), PcgError<'tcx>> {
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
    ) -> Result<(), PcgError<'tcx>> {
        for edge in edges {
            let borrow_edge: BorrowPcgEdge<'tcx> =
                BorrowPcgEdge::new(edge.value.into(), edge.conditions);
            self.apply_action(
                BorrowPcgAction::remove_edge(borrow_edge, context.to_owned()).into(),
            )?;
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
            let ref_place = deref_place.parent_place().unwrap();
            // Perhaps the place isn't yet a leaf(e.g. the ref itself is conditionally borrowed)
            // In that case we shouldn't restore its caps
            if self.pcg.is_leaf_place(ref_place, self.ctxt) {
                self.restore_place(
                    ref_place,
                    &format!("{context}: remove_deref_edges_to: restore parent place"),
                )?;
            }
        }
        Ok(())
    }

    #[tracing::instrument(skip(self, edge))]
    pub(crate) fn remove_edge_and_perform_associated_state_updates(
        &mut self,
        edge: &BorrowPcgEdge<'tcx>,
        context: &str,
    ) -> Result<(), PcgError<'tcx>> {
        if let BorrowPcgEdgeKind::Deref(deref) = edge.kind() {
            return self.remove_deref_edges_to(
                deref.deref_place,
                vec![Conditioned::new(*deref, edge.conditions.clone())]
                    .into_iter()
                    .collect(),
                context,
            );
        }
        self.record_and_apply_action(
            BorrowPcgAction::remove_edge(edge.clone(), context.to_owned()).into(),
        )?;

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
                self.pcg.as_ref().get(place, self.ctxt),
                CapabilityKind::Write | CapabilityKind::None(())
            )
        } else {
            false
        };

        self.update_unblocked_node_capabilities_and_remove_placeholder_projections(&edge.value)?;

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
                                    rp.display_string(self.ctxt.bc_ctxt())
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
                {
                    let existing_cap = self.pcg.as_ref().get(place, self.ctxt);
                    self.record_and_apply_action(
                        BorrowPcgAction::weaken(
                            place,
                            existing_cap.expect_concrete().into_positive().unwrap(),
                            CapabilityKind::Write,
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
    ) -> Result<(), PcgError<'tcx>> {
        self.record_and_apply_action(
            BorrowPcgAction::remove_lifetime_projection_label(
                deref.blocked_lifetime_projection,
                format!("{context}: unlabel blocked_region_projections"),
            )
            .into(),
        )?;
        Ok(())
    }

    pub(crate) fn record_and_apply_action(
        &mut self,
        action: PcgAction<'tcx>,
    ) -> Result<(), PcgError<'tcx>>
    where
        Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>,
    {
        tracing::debug!(
            "Applying Action: {}",
            action.debug_line(self.ctxt.bc_ctxt())
        );
        let analysis_ctxt = self.ctxt;
        let result = match &action {
            PcgAction::Borrow(action) => self
                .pcg
                .borrow
                .apply_action(action.clone(), analysis_ctxt.bc_ctxt())?,
            PcgAction::Owned(owned_action) => match owned_action.kind {
                RepackOp::RegainLoanedCapability(regained_capability) => {
                    ApplyActionResult::changed_no_display()
                }
                RepackOp::Expand(expand) => {
                    self.pcg.owned.perform_expand_action(expand, analysis_ctxt);
                    ApplyActionResult::changed_no_display()
                }
                RepackOp::DerefShallowInit(from, to) => {
                    let target_places = from.expand_one_level(to, self.ctxt)?.expansion();
                    let capability_projections = self.pcg.owned[from.local].get_allocated_mut();
                    capability_projections.insert_expansion(
                        from.projection,
                        PlaceExpansion::from_places(target_places.clone(), self.ctxt),
                    );
                    ApplyActionResult::changed_no_display()
                }
                RepackOp::Collapse(collapse) => {
                    let capability_projections =
                        self.pcg.owned[collapse.local()].get_allocated_mut();
                    capability_projections.perform_collapse_action(collapse, analysis_ctxt);
                    ApplyActionResult::changed_no_display()
                }
                RepackOp::Weaken(weaken) => {
                    pcg_validity_assert!(self.pcg.place_capability_equals(
                        weaken.place,
                        weaken.from,
                        analysis_ctxt
                    ));
                    ApplyActionResult::changed_no_display()
                }
                _ => unreachable!(),
            },
        };
        let location = self.location();

        if let Some(phase) = self.phase()
            && let Some(actions) = &mut self.actions
        {
            // Note: We create the PcgRef here to work around lifetime issues
            let pcg_ref = PcgRef {
                owned: self.pcg.owned,
                borrow: self.pcg.borrow.as_ref(),
            };
            #[cfg(feature = "visualization")]
            if let Some(analysis_ctxt) = self.ctxt.try_into_analysis_ctxt() {
                analysis_ctxt.generate_pcg_debug_visualization_graph(
                    location,
                    crate::visualization::stmt_graphs::ToGraph::Action(phase, actions.len()),
                    pcg_ref,
                );
            }
            actions.push(AppliedAction::new(action, result));
        }
        Ok(())
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
    fn apply_action(&mut self, action: PcgAction<'tcx>) -> Result<(), PcgError<'tcx>> {
        self.record_and_apply_action(action)
    }
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
    ) -> Result<(), PcgError<'tcx>> {
        let obtain_cap = obtain_type.min_required_capability_to_obtain(place, self.ctxt);

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

        let current_cap = self.pcg.as_ref().get(place, self.ctxt);

        // STEP 2
        if current_cap.is_none()
            || matches!(
                current_cap.partial_cmp(&obtain_cap),
                Some(Ordering::Less) | None
            )
        {
            // If we want to get e.g. write permission but we currently have
            // read permission, we will obtain read with the collapse and then
            // upgrade in the subsequent step
            let collapse_cap = if current_cap.is_read() {
                PositiveCapability::Read
            } else {
                obtain_cap
            };
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
            self.render_debug_graph(None, "after step 3");
        }

        self.expand_to(place, obtain_type, self.ctxt)?;

        if let ObtainType::ForStorageDead = obtain_type
            && self
                .pcg
                .place_capability_equals(place, PositiveCapability::Exclusive, self.ctxt)
        {
            self.record_and_apply_action(PcgAction::Owned(OwnedPcgAction::new(
                RepackOp::Weaken(Weaken::new(
                    place,
                    PositiveCapability::Exclusive,
                    PositiveCapability::Write,
                )),
                None,
            )))?;
        }

        self.render_debug_graph(None, "after step 5");

        // pcg_validity_assert!(
        //     self.pcg.capabilities.get(place.into()).is_some(),
        //     "{:?}: Place {:?} does not have a capability after obtain {:?}",
        //     self.location,
        //     place,
        //     obtain_type.capability()
        // );
        // pcg_validity_assert!(
        //     self.pcg.capabilities.get(place.into()).unwrap() >= capability,
        //     "{:?} Capability {:?} for {:?} is not greater than {:?}",
        //     location,
        //     self.pcg.capabilities.get(place.into()).unwrap(),
        //     place,
        //     capability
        // );
        Ok(())
    }
}

impl<'pcg, 'a: 'pcg, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PlaceExpander<'a, 'tcx>
    for PlaceObtainer<'pcg, 'a, 'tcx, Ctxt>
{
    fn contains_owned_expansion_to(&self, target: Place<'tcx>) -> bool {
        self.pcg.owned[target.local]
            .get_allocated()
            .contains_projection_to(&target.projection)
    }

    fn borrows_graph(&self) -> &crate::borrow_pcg::graph::BorrowsGraph<'tcx> {
        self.pcg.borrow.graph
    }

    fn path_conditions(&self) -> crate::borrow_pcg::validity_conditions::ValidityConditions {
        self.pcg.borrow.validity_conditions.clone()
    }

    fn location(&self) -> mir::Location {
        self.location
    }

    #[tracing::instrument(skip(self, base_place, obtain_type, ctxt), level = "warn", fields(location = ?self.location))]
    fn capability_for_expand(
        &self,
        base_place: Place<'tcx>,
        obtain_type: ObtainType,
        ctxt: impl HasCompilerCtxt<'a, 'tcx> + DebugCtxt,
    ) -> EdgeMutability {
        obtain_type.mutability(
            base_place,
            ctxt,
        )
    }
}
