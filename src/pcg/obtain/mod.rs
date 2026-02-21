pub(crate) mod expand;

use std::marker::PhantomData;

use crate::{
    action::{AppliedActions, BorrowPcgAction, OwnedPcgAction, PcgAction},
    borrow_pcg::{
        action::LabelPlaceReason,
        borrow_pcg_edge::BorrowPcgEdge,
        edge::{
            borrow_flow::{BorrowFlowEdge, BorrowFlowEdgeKind},
            kind::BorrowPcgEdgeType,
        },
        edge_data::LabelNodePredicate,
        has_pcs_elem::{LabelNodeContext, SetLabel, SourceOrTarget},
        region_projection::{HasRegions, LifetimeProjection, LocalLifetimeProjection},
        state::BorrowStateMutRef,
    },
    error::PcgError,
    r#loop::PlaceUsageType,
    owned_pcg::{LocalExpansions, OwnedPcgNode, RepackCollapse, RepackOp},
    pcg::{
        LabelPlaceConditionally, PcgMutRef, PcgRefLike, PositiveCapability, ctxt::AnalysisCtxt,
        edge::EdgeMutability, place_capabilities::PlaceCapabilitiesReader,
    },
    rustc_interface::middle::mir,
    utils::{
        CompilerCtxt, DataflowCtxt, DebugCtxt, DebugImgcat, HasBorrowCheckerCtxt, HasCompilerCtxt,
        Place, PlaceLike, SnapshotLocation, data_structures::HashSet,
        display::DisplayWithCompilerCtxt,
    },
};

pub(crate) struct PlaceObtainer<'state, 'a, 'tcx, Ctxt = AnalysisCtxt<'a, 'tcx>> {
    pub(crate) pcg: PcgMutRef<'state, 'tcx>,
    pub(crate) ctxt: Ctxt,
    pub(crate) actions: Option<&'state mut AppliedActions<'tcx>>,
    pub(crate) location: mir::Location,
    pub(crate) prev_snapshot_location: SnapshotLocation,
    pub(crate) _marker: PhantomData<&'a ()>,
}

impl<'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> RenderDebugGraph
    for PlaceObtainer<'_, 'a, 'tcx, Ctxt>
{
    #[cfg(feature = "visualization")]
    fn render_debug_graph(&self, debug_imgcat: Option<DebugImgcat>, comment: &str) {
        self.pcg
            .as_ref()
            .render_debug_graph(self.location(), debug_imgcat, comment, self.ctxt);
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
        actions: Option<&'state mut AppliedActions<'tcx>>,
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
    ForStorageDead,
    Capability(PositiveCapability),
    TwoPhaseExpand,
    LoopInvariant {
        is_blocked: bool,
        usage_type: PlaceUsageType,
    },
}

impl ObtainType {
    pub(crate) fn min_required_capability_to_obtain<'a, 'tcx>(
        self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> PositiveCapability
    where
        'tcx: 'a,
    {
        match self {
            ObtainType::ForStorageDead => PositiveCapability::Write,
            ObtainType::Capability(capability_kind) => capability_kind,
            ObtainType::TwoPhaseExpand => PositiveCapability::Read,
            ObtainType::LoopInvariant { usage_type, .. } => {
                if usage_type == PlaceUsageType::Read
                    || place.is_shared_ref(ctxt)
                    || place.projects_shared_ref(ctxt)
                {
                    PositiveCapability::Read
                } else {
                    PositiveCapability::Exclusive
                }
            }
        }
    }

    pub(crate) fn mutability<'a, 'tcx>(
        self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> EdgeMutability
    where
        'tcx: 'a,
    {
        match self {
            ObtainType::ForStorageDead => EdgeMutability::Mutable,
            ObtainType::Capability(cap) => {
                if !cap.is_read() {
                    EdgeMutability::Mutable
                } else {
                    EdgeMutability::Immutable
                }
            }
            ObtainType::TwoPhaseExpand => EdgeMutability::Immutable,
            ObtainType::LoopInvariant {
                is_blocked: _,
                usage_type,
            } => {
                if usage_type == PlaceUsageType::Read
                    || place.is_shared_ref(ctxt)
                    || place.projects_shared_ref(ctxt)
                {
                    EdgeMutability::Immutable
                } else {
                    EdgeMutability::Mutable
                }
            }
        }
    }

    pub(crate) fn should_label_rp<'a, 'tcx>(
        self,
        rp: LifetimeProjection<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        match self {
            ObtainType::ForStorageDead | ObtainType::TwoPhaseExpand => true,
            ObtainType::Capability(cap) => !cap.is_read(),
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

use LabelForLifetimeProjection::{
    ExistingLabelOfTwoPhaseReservation, NewLabelAtCurrentLocation, NoLabel,
};
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

    fn leaf_places(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> HashSet<Place<'tcx>>;

    /// Collapses owned places and performs appropriate updates to lifetime projections.
    fn collapse_owned_places_and_lifetime_projections_to(
        &mut self,
        place: Place<'tcx>,
        capability: PositiveCapability,
        context: String,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<(), PcgError<'tcx>> {
        let local_expansions = self.get_local_expansions(place.local);
        let place = place.nearest_owned_place(ctxt).with_inherent_region(ctxt);
        let Some(subtree) = local_expansions
            .find_subtree(place.projection)
            .subtree()
        else {
            return Ok(());
        };
        for pe in subtree.expansions_longest_first(place, ctxt).unwrap() {
            self.apply_action(PcgAction::Owned(OwnedPcgAction::new(
                RepackOp::Collapse(RepackCollapse::new(pe.place, capability, pe.guide())),
                Some(context.clone().into()),
            )))?;
            for rp in pe.place.lifetime_projections(ctxt) {
                let rp_expansion: Vec<LocalLifetimeProjection<'tcx>> = place
                    .expansion_places(&pe.expansion, ctxt)
                    .unwrap()
                    .into_iter()
                    .flat_map(|ep| {
                        ep.lifetime_projections(ctxt)
                            .into_iter()
                            .filter(|erp| erp.region(ctxt.ctxt()) == rp.region(ctxt.ctxt()))
                            .map(std::convert::Into::into)
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>();
                if rp_expansion.len() > 1 && capability.is_exclusive() {
                    self.create_aggregate_lifetime_projections(rp.into(), &rp_expansion, ctxt)?;
                }
            }
        }

        Ok(())
    }

    /// Only for owned places.
    fn create_aggregate_lifetime_projections<Ctxt: HasBorrowCheckerCtxt<'a, 'tcx> + DebugCtxt>(
        &mut self,
        base: LocalLifetimeProjection<'tcx>,
        expansion: &[LocalLifetimeProjection<'tcx>],
        ctxt: Ctxt,
    ) -> Result<(), PcgError<'tcx>> {
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
                let mut replacements = HashSet::default();
                node.label_place_conditionally(
                    &mut replacements,
                    &LabelNodePredicate::PlaceEquals((*place).into()),
                    &labeller,
                    LabelNodeContext::new(
                        SourceOrTarget::Source,
                        BorrowPcgEdgeType::BorrowFlow {
                            future_edge_kind: None,
                        },
                    ),
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
                    )
                    .into(),
                    self.borrows_state().validity_conditions.clone(),
                );
                self.apply_action(
                    BorrowPcgAction::add_edge(edge, "create_aggregate_lifetime_projections").into(),
                )?;
            }
        }
        Ok(())
    }
}

pub(crate) trait ActionApplier<'tcx> {
    fn apply_action(&mut self, action: PcgAction<'tcx>) -> Result<(), PcgError<'tcx>>;
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
