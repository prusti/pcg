pub(crate) mod expand;

use std::marker::PhantomData;

use crate::{
    action::{BorrowPcgAction, OwnedPcgAction, PcgAction},
    borrow_pcg::{
        action::LabelPlaceReason,
        borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike},
        edge::{
            kind::BorrowPcgEdgeKind,
            outlives::{BorrowFlowEdge, BorrowFlowEdgeKind},
        },
        edge_data::LabelPlacePredicate,
        has_pcs_elem::{LabelNodeContext, LabelPlaceWithContext, SetLabel},
        region_projection::{LifetimeProjection, LocalLifetimeProjection},
        state::BorrowStateMutRef,
    },
    error::PcgError,
    r#loop::PlaceUsageType,
    owned_pcg::{LocalExpansions, RepackCollapse, RepackOp},
    pcg::{
        CapabilityKind, PcgMutRef, PcgRefLike,
        ctxt::AnalysisCtxt,
        place_capabilities::{
            PlaceCapabilitiesInterface, PlaceCapabilitiesReader, SymbolicPlaceCapabilities,
        },
    },
    rustc_interface::middle::mir,
    utils::{
        CompilerCtxt, DataflowCtxt, DebugImgcat, HasBorrowCheckerCtxt, HasCompilerCtxt, HasPlace,
        Place, SnapshotLocation, data_structures::HashSet, display::DisplayWithCompilerCtxt,
    },
};

pub(crate) struct PlaceObtainer<'state, 'a, 'tcx, Ctxt = AnalysisCtxt<'a, 'tcx>> {
    pub(crate) pcg: PcgMutRef<'state, 'tcx>,
    pub(crate) ctxt: Ctxt,
    pub(crate) actions: Option<&'state mut Vec<PcgAction<'tcx>>>,
    pub(crate) location: mir::Location,
    pub(crate) prev_snapshot_location: SnapshotLocation,
    pub(crate) _marker: PhantomData<&'a ()>,
}

impl<'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> RenderDebugGraph
    for PlaceObtainer<'_, 'a, 'tcx, Ctxt>
{
    #[cfg(feature = "visualization")]
    fn render_debug_graph(&self, debug_imgcat: Option<DebugImgcat>, comment: &str) {
        self.pcg.as_ref().render_debug_graph(
            self.location(),
            debug_imgcat,
            comment,
            self.ctxt.bc_ctxt(),
        );
    }
}

impl<Ctxt> HasSnapshotLocation for PlaceObtainer<'_, '_, '_, Ctxt> {
    fn prev_snapshot_location(&self) -> SnapshotLocation {
        self.prev_snapshot_location
    }
}

impl<'state, 'tcx, Ctxt> PlaceObtainer<'state, '_, 'tcx, Ctxt> {
    pub(crate) fn location(&self) -> mir::Location {
        self.location
    }

    pub(crate) fn new(
        pcg: PcgMutRef<'state, 'tcx>,
        actions: Option<&'state mut Vec<PcgAction<'tcx>>>,
        ctxt: Ctxt,
        location: mir::Location,
        prev_snapshot_location: SnapshotLocation,
    ) -> Self {
        Self {
            pcg,
            ctxt,
            actions,
            location,
            prev_snapshot_location,
            _marker: PhantomData,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ObtainType {
    Capability(CapabilityKind),
    TwoPhaseExpand,
    LoopInvariant {
        is_blocked: bool,
        usage_type: PlaceUsageType,
    },
}

impl ObtainType {
    /// The capability to use when generating expand annotations.
    ///
    /// If the expansion is for a place e.g. `x.f` where `x` currently has
    /// Exclusive capability, and the obtain is for Write capability, then
    /// expansion will have Exclusive capability (subsequently a Weaken
    /// annotation will be generated for the target place to downgrade it from
    /// Exclusive to Write). This ensures that other fields of `x` retain their
    /// Exclusive capability.
    ///
    /// Otherwise, the capability for the expansion is the same as the
    /// capability for the [`ObtainType`].
    pub(crate) fn capability_for_expand<'a, 'tcx>(
        &self,
        place: Place<'tcx>,
        current_cap: CapabilityKind,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> CapabilityKind
    where
        'tcx: 'a,
    {
        if let ObtainType::Capability(CapabilityKind::Write) = self
            && current_cap.is_exclusive()
        {
            CapabilityKind::Exclusive
        } else {
            self.capability(place, ctxt)
        }
    }
    pub(crate) fn capability<'a, 'tcx>(
        self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> CapabilityKind
    where
        'tcx: 'a,
    {
        match self {
            ObtainType::Capability(cap) => cap,
            ObtainType::TwoPhaseExpand => CapabilityKind::Read,
            ObtainType::LoopInvariant {
                is_blocked: _,
                usage_type,
            } => {
                if usage_type == PlaceUsageType::Read
                    || place.is_shared_ref(ctxt)
                    || place.projects_shared_ref(ctxt)
                {
                    CapabilityKind::Read
                } else {
                    CapabilityKind::Exclusive
                }
            }
        }
    }

    pub(crate) fn should_label_rp<'a, 'tcx>(
        &self,
        rp: LifetimeProjection<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        match self {
            ObtainType::Capability(cap) => !cap.is_read(),
            ObtainType::TwoPhaseExpand => true,
            ObtainType::LoopInvariant { .. } => rp.base.is_mutable(ctxt),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum LabelForLifetimeProjection {
    NewLabelAtCurrentLocation(SnapshotLocation),
    ExistingLabelOfTwoPhaseReservation(SnapshotLocation),
    NoLabel,
}

use LabelForLifetimeProjection::*;
impl LabelForLifetimeProjection {
    fn label(self) -> Option<SnapshotLocation> {
        match self {
            NewLabelAtCurrentLocation(label) | ExistingLabelOfTwoPhaseReservation(label) => {
                Some(label)
            }
            NoLabel => None,
        }
    }
}

// TODO: The edges that are added here could just be part of the collapse "action" probably
pub(crate) trait PlaceCollapser<'a, 'tcx: 'a>:
    HasSnapshotLocation + ActionApplier<'tcx>
{
    fn get_local_expansions(&self, local: mir::Local) -> &LocalExpansions<'tcx>;

    fn borrows_state(&mut self) -> BorrowStateMutRef<'_, 'tcx>;

    fn capabilities(&mut self) -> &mut SymbolicPlaceCapabilities<'tcx>;

    fn leaf_places(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> HashSet<Place<'tcx>>;

    fn restore_capability_to_leaf_places(
        &mut self,
        parent_place: Option<Place<'tcx>>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<(), PcgError> {
        let mut leaf_places = self.leaf_places(ctxt.bc_ctxt());
        tracing::debug!(
            "Leaf places: {}",
            leaf_places.to_short_string(ctxt.bc_ctxt())
        );
        leaf_places.retain(|p| {
            self.capabilities().get(*p, ctxt) == Some(CapabilityKind::Read.into())
                && !p.projects_shared_ref(ctxt)
                && p.parent_place()
                    .is_none_or(|parent| self.capabilities().get(parent, ctxt).is_none())
        });
        tracing::debug!(
            "Restoring capability to leaf places: {}",
            leaf_places.to_short_string(ctxt.bc_ctxt())
        );
        for place in leaf_places {
            if let Some(parent_place) = parent_place
                && !parent_place.is_prefix_of(place)
            {
                continue;
            }
            let action = PcgAction::restore_capability(
                place,
                CapabilityKind::Exclusive,
                "restore capability to leaf place",
                ctxt,
            );
            self.apply_action(action)?;
        }
        Ok(())
    }

    #[tracing::instrument(skip(self, place, ctxt))]
    fn label_and_remove_capabilities_for_deref_projections_of_postfix_places(
        &mut self,
        place: Place<'tcx>,
        shared_refs_only: bool,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<bool, PcgError> {
        let place_predicate = |p| {
            if !place.is_strict_prefix_of(p) {
                return false;
            }
            if shared_refs_only {
                p.is_shared_ref(ctxt)
            } else {
                p.is_ref(ctxt)
            }
        };
        let derefs_to_disconnect = self
            .borrows_state()
            .graph
            .edges()
            .flat_map(|e| match e.kind() {
                BorrowPcgEdgeKind::Deref(e)
                    if let Some(p) = e.blocked_place.as_current_place()
                        && place_predicate(p) =>
                {
                    Some(*e)
                }
                _ => None,
            })
            .collect::<Vec<_>>();

        for mut rp in derefs_to_disconnect.iter().copied() {
            tracing::debug!(
                "Disconnecting deref projection {}",
                rp.to_short_string(ctxt.bc_ctxt())
            );
            let conditions = self.borrows_state().graph.remove(&rp.into()).unwrap();
            let label = self.prev_snapshot_location();
            rp.blocked_place.label_place_with_context(
                &LabelPlacePredicate::Exact(rp.blocked_place.place()),
                &SetLabel(label),
                LabelNodeContext::Other,
                ctxt.bc_ctxt(),
            );
            self.capabilities()
                .remove_all_postfixes(rp.deref_place.as_current_place().unwrap(), ctxt);
            rp.deref_place.label_place_with_context(
                &LabelPlacePredicate::Exact(rp.deref_place.place()),
                &SetLabel(self.prev_snapshot_location()),
                LabelNodeContext::TargetOfExpansion,
                ctxt.bc_ctxt(),
            );
            self.apply_action(
                BorrowPcgAction::add_edge(
                    BorrowPcgEdge::new(rp.into(), conditions.clone()),
                    format!(
                        "label_deref_projections_of_postfix_places. Shared refs only: {shared_refs_only}"
                    ),
                    ctxt,
                )
                .into(),
            )?;
        }
        // TODO: This could be a hack
        if !derefs_to_disconnect.is_empty() {
            tracing::debug!(
                "Labeling deref projections for place {}",
                place.to_short_string(ctxt.ctxt())
            );
            self.apply_action(
                BorrowPcgAction::label_place_and_update_related_capabilities(
                    place,
                    self.prev_snapshot_location(),
                    LabelPlaceReason::LabelDerefProjections { shared_refs_only },
                )
                .into(),
            )?;
        }
        Ok(true)
    }

    /// Collapses owned places and performs appropriate updates to lifetime projections.
    fn collapse_owned_places_and_lifetime_projections_to(
        &mut self,
        place: Place<'tcx>,
        capability: CapabilityKind,
        context: String,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<(), PcgError> {
        let to_collapse = self
            .get_local_expansions(place.local)
            .places_to_collapse_for_obtain_of(place, ctxt);
        tracing::debug!(
            "To obtain {}, will collapse {}",
            place.to_short_string(ctxt.ctxt()),
            to_collapse.to_short_string(ctxt.ctxt())
        );
        for place in to_collapse {
            let expansions = self
                .get_local_expansions(place.local)
                .expansions_from(place)
                .cloned()
                .collect::<Vec<_>>();
            self.apply_action(PcgAction::Owned(OwnedPcgAction::new(
                RepackOp::Collapse(RepackCollapse::new(place, capability)),
                Some(context.clone()),
            )))?;
            for pe in expansions {
                for rp in place.lifetime_projections(ctxt) {
                    let rp_expansion: Vec<LocalLifetimeProjection<'tcx>> = place
                        .expansion_places(&pe.expansion, ctxt)
                        .unwrap()
                        .into_iter()
                        .flat_map(|ep| {
                            ep.lifetime_projections(ctxt)
                                .into_iter()
                                .filter(|erp| erp.region(ctxt.ctxt()) == rp.region(ctxt.ctxt()))
                                .map(|erp| erp.into())
                                .collect::<Vec<_>>()
                        })
                        .collect::<Vec<_>>();
                    if rp_expansion.len() > 1 && capability.is_exclusive() {
                        self.create_aggregate_lifetime_projections(rp.into(), &rp_expansion, ctxt)?;
                    }
                }
            }
        }

        Ok(())
    }

    /// Only for owned places.
    fn create_aggregate_lifetime_projections(
        &mut self,
        base: LocalLifetimeProjection<'tcx>,
        expansion: &[LocalLifetimeProjection<'tcx>],
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<(), PcgError> {
        for (idx, node) in expansion.iter().enumerate() {
            if let Some(place) = node.base.as_current_place() {
                let labeller = SetLabel(self.prev_snapshot_location());
                self.borrows_state().graph.label_place(
                    (*place).into(),
                    LabelPlaceReason::Collapse,
                    &labeller,
                    ctxt,
                );
                let mut node = *node;
                node.label_place_with_context(
                    &LabelPlacePredicate::Exact((*place).into()),
                    &labeller,
                    LabelNodeContext::Other,
                    ctxt.bc_ctxt(),
                );
                let edge = BorrowPcgEdge::new(
                    BorrowFlowEdge::new(
                        node.into(),
                        base,
                        BorrowFlowEdgeKind::Aggregate {
                            field_idx: idx,
                            target_rp_index: 0, // TODO
                        },
                        ctxt,
                    )
                    .into(),
                    self.borrows_state().validity_conditions.clone(),
                );
                self.apply_action(
                    BorrowPcgAction::add_edge(edge, "create_aggregate_lifetime_projections", ctxt)
                        .into(),
                )?;
            }
        }
        Ok(())
    }
}

pub(crate) trait ActionApplier<'tcx> {
    fn apply_action(&mut self, action: PcgAction<'tcx>) -> Result<bool, PcgError>;
}

pub(crate) trait HasSnapshotLocation {
    /// The snapshot location to use when e.g. moving out a place. Before
    /// performing such an action on a place, we would first update references
    /// to the place to use the version that is *labelled* with the location
    /// returned by this function (indicating that it refers to the value in the
    /// place before the action).
    fn prev_snapshot_location(&self) -> SnapshotLocation;
}

pub(crate) trait RenderDebugGraph {
    #[cfg(feature = "visualization")]
    fn render_debug_graph(&self, debug_imgcat: Option<DebugImgcat>, comment: &str);

    #[cfg(not(feature = "visualization"))]
    fn render_debug_graph(&self, debug_imgcat: Option<DebugImgcat>, comment: &str) {}
}
