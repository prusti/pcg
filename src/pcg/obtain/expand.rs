use crate::{
    action::{BorrowPcgAction, OwnedPcgAction},
    borrow_checker::r#impl::get_reserve_location,
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike, LocalNode},
        borrow_pcg_expansion::{BorrowPcgExpansion, PlaceExpansion},
        edge::{
            deref::DerefEdge,
            kind::BorrowPcgEdgeKind,
            outlives::{BorrowFlowEdge, BorrowFlowEdgeKind},
        },
        graph::BorrowsGraph,
        has_pcs_elem::{LabelLifetimeProjection, LabelLifetimeProjectionPredicate},
        path_condition::ValidityConditions,
        region_projection::{LifetimeProjection, LocalLifetimeProjection},
    },
    error::PcgError,
    owned_pcg::{ExpandedPlace, RepackOp},
    pcg::{
        CapabilityKind, PcgNodeLike,
        obtain::{
            ActionApplier, HasSnapshotLocation, LabelForLifetimeProjection, ObtainType,
            RenderDebugGraph,
        },
        place_capabilities::BlockType,
    },
    rustc_interface::middle::mir,
    utils::{
        CompilerCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, HasPlace, Place, ProjectionKind,
        ShallowExpansion, SnapshotLocation, display::DisplayWithCompilerCtxt,
    },
};

pub(crate) trait PlaceExpander<'a, 'tcx: 'a>:
    HasSnapshotLocation + ActionApplier<'tcx> + RenderDebugGraph
{
    fn contains_owned_expansion_to(&self, target: Place<'tcx>) -> bool;

    fn update_capabilities_for_borrow_expansion(
        &mut self,
        expansion: &BorrowPcgExpansion<'tcx>,
        block_type: BlockType,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError>;

    fn update_capabilities_for_deref(
        &mut self,
        ref_place: Place<'tcx>,
        capability: CapabilityKind,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError>;

    #[tracing::instrument(skip(self, obtain_type, ctxt))]
    fn expand_to(
        &mut self,
        place: Place<'tcx>,
        obtain_type: ObtainType,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<(), PcgError> {
        for (base, _) in place.iter_projections(ctxt.ctxt()) {
            let base = base.with_inherent_region(ctxt);
            let expansion = base.expand_one_level(place, ctxt)?;
            if self.expand_place_one_level(base, &expansion, obtain_type, ctxt)? {
                tracing::debug!(
                    "expand region projections for {} one level",
                    base.to_short_string(ctxt.ctxt())
                );
                self.expand_lifetime_projections_one_level(base, &expansion, obtain_type, ctxt)?;
            }
        }
        Ok(())
    }

    fn label_for_rp(
        &self,
        rp: LifetimeProjection<'tcx, Place<'tcx>>,
        obtain_type: ObtainType,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> LabelForLifetimeProjection {
        use LabelForLifetimeProjection::*;
        if obtain_type.should_label_rp(rp.rebase(), ctxt) {
            NewLabelAtCurrentLocation(self.prev_snapshot_location())
        } else {
            match self.label_for_shared_expansion_of_rp(rp, ctxt) {
                Some(label) => ExistingLabelOfTwoPhaseReservation(label),
                None => NoLabel,
            }
        }
    }

    /// If the base of `rp` is blocked by a two-phase borrow, we want to use the
    /// existing label of its expansion
    fn label_for_shared_expansion_of_rp(
        &self,
        rp: LifetimeProjection<'tcx, Place<'tcx>>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Option<SnapshotLocation> {
        ctxt.bc()
            .borrows_blocking(rp.base, self.location(), ctxt.bc_ctxt())
            .first()
            .map(|borrow| {
                let borrow_reserve_location = get_reserve_location(borrow);
                SnapshotLocation::after_statement_at(borrow_reserve_location, ctxt)
            })
    }

    fn capability_for_expand(
        &self,
        base_place: Place<'tcx>,
        obtain_type: ObtainType,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> CapabilityKind;

    fn expand_owned_place_one_level(
        &mut self,
        base: Place<'tcx>,
        expansion: &ShallowExpansion<'tcx>,
        obtain_type: ObtainType,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Result<bool, PcgError> {
        if self.contains_owned_expansion_to(expansion.target_place) {
            tracing::debug!(
                "Already contains owned expansion from {}",
                base.to_short_string(ctxt.ctxt())
            );
            return Ok(false);
        }
        tracing::debug!(
            "New owned expansion from {}",
            base.to_short_string(ctxt.ctxt())
        );
        if expansion.kind.is_deref_box()
            && obtain_type.capability(base, ctxt).is_shallow_exclusive()
        {
            self.apply_action(
                OwnedPcgAction::new(
                    RepackOp::DerefShallowInit(expansion.base_place(), expansion.target_place),
                    None,
                )
                .into(),
            )?;
        } else {
            self.apply_action(
                OwnedPcgAction::new(
                    RepackOp::expand(
                        expansion.base_place(),
                        expansion.guide(),
                        self.capability_for_expand(expansion.base_place(), obtain_type, ctxt),
                        ctxt,
                    ),
                    Some(format!("Expand owned place one level ({:?})", obtain_type)),
                )
                .into(),
            )?;
        }
        Ok(true)
    }

    fn expand_place_one_level(
        &mut self,
        base: Place<'tcx>,
        expansion: &ShallowExpansion<'tcx>,
        obtain_type: ObtainType,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<bool, PcgError> {
        let place_expansion = PlaceExpansion::from_places(expansion.expansion(), ctxt);
        if matches!(expansion.kind, ProjectionKind::DerefRef(_)) {
            if self
                .borrows_graph()
                .contains_deref_edge_to(base.project_deref(ctxt))
            {
                return Ok(false);
            }
            let blocked_lifetime_projection_label = if base.is_mut_ref(ctxt) {
                Some(self.prev_snapshot_location())
            } else {
                self.label_for_shared_expansion_of_rp(
                    base.base_lifetime_projection(ctxt).unwrap(),
                    ctxt,
                )
            };
            let deref = DerefEdge::new(base, blocked_lifetime_projection_label, ctxt);
            self.render_debug_graph(None, "expand_place_one_level: before apply action");
            let action = BorrowPcgAction::add_edge(
                BorrowPcgEdge::new(deref.into(), self.path_conditions()),
                "expand_place_one_level: add deref edge",
                ctxt,
            );
            self.apply_action(action.into())?;
            self.render_debug_graph(None, "expand_place_one_level: after apply action");
            self.update_capabilities_for_deref(
                base,
                obtain_type.capability(base, ctxt),
                ctxt.bc_ctxt(),
            )?;
            self.render_debug_graph(
                None,
                "expand_place_one_level: after update_capabilities_for_deref",
            );
            if deref.blocked_lifetime_projection.label().is_some() {
                self.apply_action(
                    BorrowPcgAction::label_lifetime_projection(
                        LabelLifetimeProjectionPredicate::Equals(
                            deref.blocked_lifetime_projection.with_label(None, ctxt),
                        ),
                        deref.blocked_lifetime_projection.label(),
                        "block deref",
                    )
                    .into(),
                )?;
            }
            Ok(true)
        } else if base.is_owned(ctxt) {
            self.expand_owned_place_one_level(base, expansion, obtain_type, ctxt)
        } else {
            self.add_borrow_pcg_expansion(base, place_expansion, obtain_type, ctxt)
        }
    }

    fn location(&self) -> mir::Location;

    fn borrows_graph(&self) -> &BorrowsGraph<'tcx>;

    fn path_conditions(&self) -> ValidityConditions;

    fn add_borrow_pcg_expansion(
        &mut self,
        base: Place<'tcx>,
        place_expansion: PlaceExpansion<'tcx>,
        obtain_type: ObtainType,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<bool, PcgError>
    where
        'tcx: 'a,
    {
        let expanded_place = ExpandedPlace {
            place: base,
            expansion: place_expansion,
        };
        if self
            .borrows_graph()
            .contains_borrow_pcg_expansion(&expanded_place, ctxt)?
        {
            return Ok(false);
        }
        tracing::debug!(
            "Create expansion from {}",
            base.to_short_string(ctxt.bc_ctxt())
        );
        let block_type = expanded_place.expansion.block_type(base, obtain_type, ctxt);
        tracing::debug!(
            "Block type for {} is {:?}",
            base.to_short_string(ctxt.bc_ctxt()),
            block_type
        );
        let expansion: BorrowPcgExpansion<'tcx, LocalNode<'tcx>> =
            BorrowPcgExpansion::new(base.into(), expanded_place.expansion, ctxt)?;

        self.render_debug_graph(
            None,
            &format!(
                "add_borrow_pcg_expansion: before update_capabilities_for_borrow_expansion {}",
                expansion.to_short_string(ctxt.bc_ctxt())
            ),
        );
        self.update_capabilities_for_borrow_expansion(&expansion, block_type, ctxt.bc_ctxt())?;
        self.render_debug_graph(
            None,
            "add_borrow_pcg_expansion: after update_capabilities_for_borrow_expansion",
        );
        let action = BorrowPcgAction::add_edge(
            BorrowPcgEdge::new(
                BorrowPcgEdgeKind::BorrowPcgExpansion(expansion),
                self.path_conditions(),
            ),
            "add_borrow_pcg_expansion",
            ctxt,
        );
        self.apply_action(action.into())?;
        Ok(true)
    }

    #[tracing::instrument(skip(self, base, expansion, ctxt))]
    fn expand_lifetime_projections_one_level(
        &mut self,
        base: Place<'tcx>,
        expansion: &ShallowExpansion<'tcx>,
        obtain_type: ObtainType,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<(), PcgError> {
        for base_rp in base.lifetime_projections(ctxt) {
            if let Some(place_expansion) =
                expansion.place_expansion_for_region(base_rp.region(ctxt.ctxt()), ctxt)
            {
                tracing::debug!("Expand {}", base_rp.to_short_string(ctxt.bc_ctxt()));
                let mut expansion = BorrowPcgExpansion::new(base_rp.into(), place_expansion, ctxt)?;
                let expansion_label = self.label_for_rp(base_rp, obtain_type, ctxt);
                if let Some(label) = expansion_label.label() {
                    expansion.label_lifetime_projection(
                        &LabelLifetimeProjectionPredicate::Equals(base_rp.into()),
                        Some(label.into()),
                        ctxt.bc_ctxt(),
                    );
                }
                self.apply_action(
                    BorrowPcgAction::add_edge(
                        BorrowPcgEdge::new(
                            BorrowPcgEdgeKind::BorrowPcgExpansion(expansion.clone()),
                            self.path_conditions(),
                        ),
                        "expand_region_projections_one_level",
                        ctxt,
                    )
                    .into(),
                )?;
                if let LabelForLifetimeProjection::NewLabelAtCurrentLocation(label) =
                    expansion_label
                {
                    self.apply_action(
                        BorrowPcgAction::label_lifetime_projection(
                            LabelLifetimeProjectionPredicate::Equals(base_rp.into()),
                            Some(label.into()),
                            "expand_region_projections_one_level: create new RP label",
                        )
                        .into(),
                    )?;

                    // Don't add placeholder edges for owned expansions, unless its a deref
                    if !base.is_owned(ctxt) || base.is_mut_ref(ctxt) {
                        let old_rp_base = base_rp.with_label(Some(label.into()), ctxt);
                        let expansion_rps = expansion
                            .expansion()
                            .iter()
                            .map(|node| {
                                node.to_pcg_node(ctxt.bc_ctxt())
                                    .try_into_region_projection()
                                    .unwrap()
                            })
                            .collect::<Vec<_>>();
                        self.add_and_update_placeholder_edges(
                            old_rp_base.into(),
                            &expansion_rps,
                            "obtain",
                            ctxt,
                        )?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Performs bookkeeping for future nodes in the case where capability from
    /// (generally lablled) `origin_rp` is is temporarily transferred to
    /// (unlablled) `expansion_rps`, but will eventually be transferred back to
    /// `origin_rp`.
    ///
    /// This happens in the case of borrows and expansions of borrowed places,
    /// in which case `origin_rp` is labelled.
    /// We also use this for constructing loop abstractions where `origin_rp`
    /// is unlabelled (the labels are added in a later stage).
    ///
    /// The logic as as follows:
    ///
    /// Adds a node `future_rp` which is the future node for `origin_rp`.
    ///
    /// 1. Add a Future edge from `origin_rp` to `future_rp`
    /// 2. Add Future edges from each `expansion_rp` to `future_rp`
    /// 3. All Future edges with source `origin_rp` (except for the one
    ///    created in step 1) are modified to now have source `future_rp`
    ///
    fn add_and_update_placeholder_edges(
        &mut self,
        origin_rp: LocalLifetimeProjection<'tcx>,
        expansion_rps: &[LifetimeProjection<'tcx>],
        context: &str,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<(), PcgError> {
        if expansion_rps.is_empty() {
            return Ok(());
        }
        let future_rp = origin_rp.with_placeholder_label(ctxt);

        // Add edge {origin|r'a at l} -> {origin|r'a at FUTURE}
        self.apply_action(
            BorrowPcgAction::add_edge(
                BorrowPcgEdge::new(
                    BorrowFlowEdge::new(
                        origin_rp.into(),
                        future_rp,
                        BorrowFlowEdgeKind::Future,
                        ctxt,
                    )
                    .into(),
                    self.path_conditions(),
                ),
                format!("{}: placeholder bookkeeping", context),
                ctxt,
            )
            .into(),
        )?;

        // For each field F add edge {origin.F|'a} -> {origin|r'a at FUTURE}
        for expansion_rp in expansion_rps {
            self.apply_action(
                BorrowPcgAction::add_edge(
                    BorrowPcgEdge::new(
                        BorrowFlowEdge::new(
                            *expansion_rp,
                            future_rp,
                            BorrowFlowEdgeKind::Future,
                            ctxt,
                        )
                        .into(),
                        self.path_conditions(),
                    ),
                    format!("{}: placeholder bookkeeping", context),
                    ctxt,
                )
                .into(),
            )?;
        }
        self.redirect_source_of_future_edges(origin_rp, future_rp, ctxt)?;
        Ok(())
    }

    fn redirect_source_of_future_edges(
        &mut self,
        old_source: LocalLifetimeProjection<'tcx>,
        new_source: LocalLifetimeProjection<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<(), PcgError> {
        let to_replace = self
            .borrows_graph()
            .edges_blocking(old_source.into(), ctxt)
            .filter_map(|edge| {
                if let BorrowPcgEdgeKind::BorrowFlow(bf_edge) = edge.kind
                    && bf_edge.kind == BorrowFlowEdgeKind::Future
                    && bf_edge.short() != new_source
                {
                    return Some((
                        edge.to_owned_edge(),
                        BorrowPcgEdge::new(
                            BorrowFlowEdge::new(
                                new_source.into(),
                                bf_edge.short(),
                                BorrowFlowEdgeKind::Future,
                                ctxt,
                            )
                            .into(),
                            edge.conditions.clone(),
                        ),
                    ));
                }
                None
            })
            .collect::<Vec<_>>();
        for (to_remove, to_insert) in to_replace {
            self.apply_action(
                BorrowPcgAction::remove_edge(to_remove, "placeholder bookkeeping").into(),
            )?;
            self.apply_action(
                BorrowPcgAction::add_edge(to_insert, "placeholder bookkeeping", ctxt).into(),
            )?;
        }
        Ok(())
    }
}
