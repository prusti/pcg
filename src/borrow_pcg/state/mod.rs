//! The data structure representing the state of the Borrow PCG.

use std::{borrow::Cow, marker::PhantomData};

use crate::{
    borrow_pcg::{
        action::ApplyActionResult,
        borrow_pcg_edge::BlockingNode,
        edge_data::{LabelEdgeLifetimeProjections, LabelEdgePlaces, display_node_replacements},
        graph::join::JoinBorrowsArgs,
        region_projection::{HasRegions, OverrideRegionDebugString, PcgLifetimeProjectionBase},
        validity_conditions::{
            EMPTY_VALIDITY_CONDITIONS_REF, JoinValidityConditionsResult, ValidityConditionOps,
            ValidityConditionsLike,
        },
    },
    pcg::{
        CapabilityLike, PcgNodeWithPlace, SymbolicCapability,
        place_capabilities::{PlaceCapabilitiesReader, SymbolicPlaceCapabilities},
    },
    utils::{
        DebugCtxt, HasBorrowCheckerCtxt, HasLocals, HasTyCtxt, LocalTys, PcgPlace, PlaceLike,
        data_structures::HashSet,
        display::{DisplayWithCtxt, OutputMode},
        maybe_remote::MaybeRemotePlace,
    },
};

use super::{
    borrow_pcg_edge::{BlockedNode, BorrowPcgEdge, BorrowPcgEdgeRef},
    graph::BorrowsGraph,
    validity_conditions::{PathCondition, ValidityConditions},
    visitor::extract_regions,
};
use crate::{
    action::BorrowPcgAction,
    borrow_pcg::{
        action::{BorrowPcgActionKind, LabelPlaceReason},
        edge::{
            borrow::BorrowEdge,
            borrow_flow::{BorrowFlowEdge, BorrowFlowEdgeKind},
            kind::BorrowPcgEdgeKind,
        },
        edge_data::{EdgeData, LabelNodePredicate},
        has_pcs_elem::{PlaceLabeller, SetLabel},
        region_projection::{LifetimeProjection, LifetimeProjectionLabel},
    },
    error::PcgError,
    pcg::{
        CapabilityKind, PcgNode,
        ctxt::AnalysisCtxt,
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesInterface},
    },
    pcg_validity_assert,
    rustc_interface::middle::{
        mir::{self, BasicBlock, BorrowKind, Location, MutBorrowKind},
        ty::{self},
    },
    utils::{
        CompilerCtxt, Place, display::DebugLines, place::maybe_old::MaybeLabelledPlace,
        remote::RemotePlace, validity::HasValidityCheck,
    },
};

fn map_label_predicate<'tcx, P: Copy>(
    predicate: &LabelNodePredicate<'tcx, P>,
) -> LabelNodePredicate<'tcx, P> {
    match predicate {
        LabelNodePredicate::LifetimeProjectionLabelEquals(label) => {
            LabelNodePredicate::LifetimeProjectionLabelEquals(*label)
        }
        LabelNodePredicate::PlaceLabelEquals(location) => {
            LabelNodePredicate::PlaceLabelEquals(*location)
        }
        LabelNodePredicate::ProjectionRegionIdxEquals(region_idx) => {
            LabelNodePredicate::ProjectionRegionIdxEquals(*region_idx)
        }
        LabelNodePredicate::Equals(node) => LabelNodePredicate::Equals(*node),
        LabelNodePredicate::PlaceEquals(place) => LabelNodePredicate::PlaceEquals((*place).into()),
        LabelNodePredicate::PlaceIsPostfixOf(place) => {
            LabelNodePredicate::PlaceIsPostfixOf((*place).into())
        }
        LabelNodePredicate::NodeType(node_type) => LabelNodePredicate::NodeType(*node_type),
        LabelNodePredicate::And(predicates) => {
            LabelNodePredicate::And(predicates.iter().map(map_label_predicate).collect())
        }
        LabelNodePredicate::Or(predicates) => {
            LabelNodePredicate::Or(predicates.iter().map(map_label_predicate).collect())
        }
        LabelNodePredicate::Not(predicate) => {
            LabelNodePredicate::Not(Box::new(map_label_predicate(predicate)))
        }
        LabelNodePredicate::EdgeType(edge_type) => LabelNodePredicate::EdgeType(*edge_type),
        LabelNodePredicate::InSourceNodes => LabelNodePredicate::InSourceNodes,
        LabelNodePredicate::InTargetNodes => LabelNodePredicate::InTargetNodes,
    }
}

/// The state of the Borrow PCG, including the Borrow PCG graph and the validity
/// conditions associated with the current basic block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BorrowsState<
    'a,
    'tcx,
    EdgeKind: PartialEq + Eq + std::hash::Hash = BorrowPcgEdgeKind<'tcx>,
    VC = ValidityConditions,
> {
    pub(crate) graph: BorrowsGraph<'tcx, EdgeKind, VC>,
    pub(crate) validity_conditions: &'a VC,
}

impl<'a, 'tcx, EdgeKind: PartialEq + Eq + std::hash::Hash, VC: ValidityConditionsLike> Default
    for BorrowsState<'a, 'tcx, EdgeKind, VC>
{
    fn default() -> Self {
        Self {
            graph: BorrowsGraph::default(),
            validity_conditions: VC::EMPTY,
        }
    }
}

pub(crate) struct BorrowStateMutRef<
    'pcg,
    'tcx,
    EdgeKind = BorrowPcgEdgeKind<'tcx>,
    VC = ValidityConditions,
> {
    pub(crate) graph: &'pcg mut BorrowsGraph<'tcx, EdgeKind, VC>,
    pub(crate) validity_conditions: &'pcg VC,
}

impl<'pcg, 'tcx, EdgeKind, VC> BorrowStateMutRef<'pcg, 'tcx, EdgeKind, VC> {
    pub(crate) fn new(
        graph: &'pcg mut BorrowsGraph<'tcx, EdgeKind, VC>,
        validity_conditions: &'pcg VC,
    ) -> Self {
        Self {
            graph,
            validity_conditions,
        }
    }
}

pub(crate) struct BorrowStateRef<
    'pcg,
    'tcx,
    EdgeKind = BorrowPcgEdgeKind<'tcx>,
    VC = ValidityConditions,
> {
    pub(crate) graph: &'pcg BorrowsGraph<'tcx, EdgeKind>,
    #[allow(unused)]
    pub(crate) validity_conditions: &'pcg VC,
}

impl<'pcg, 'tcx, EdgeKind, VC> BorrowStateRef<'pcg, 'tcx, EdgeKind, VC> {
    pub(crate) fn new(
        graph: &'pcg BorrowsGraph<'tcx, EdgeKind>,
        validity_conditions: &'pcg VC,
    ) -> Self {
        Self {
            graph,
            validity_conditions,
        }
    }
}

impl<'pcg, 'tcx, EdgeKind, P: Copy> Clone for BorrowStateRef<'pcg, 'tcx, EdgeKind, P> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'pcg, 'tcx, EdgeKind, P: Copy> Copy for BorrowStateRef<'pcg, 'tcx, EdgeKind, P> {}

pub(crate) trait BorrowsStateLike<'tcx, EdgeKind = BorrowPcgEdgeKind<'tcx>, VC = ValidityConditions>
{
    fn as_mut_ref(&mut self) -> BorrowStateMutRef<'_, 'tcx, EdgeKind, VC>;
    fn as_ref(&self) -> BorrowStateRef<'_, 'tcx, EdgeKind, VC>;

    fn graph_mut(&mut self) -> &mut BorrowsGraph<'tcx, EdgeKind, VC> {
        self.as_mut_ref().graph
    }
    fn graph(&self) -> &BorrowsGraph<'tcx, EdgeKind>;

    fn label_place_and_update_related_capabilities<
        'a,
        P: PlaceLike<'tcx, Ctxt> + DisplayWithCtxt<Ctxt>,
        Ctxt: Copy + OverrideRegionDebugString,
        C,
    >(
        &mut self,
        place: P,
        reason: LabelPlaceReason,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        capabilities: &mut impl PlaceCapabilitiesInterface<'tcx, C, P>,
        ctxt: Ctxt,
    ) -> ApplyActionResult
    where
        'tcx: 'a,
        EdgeKind: LabelEdgePlaces<'tcx, Ctxt, P> + Eq + std::hash::Hash,
        PcgNodeWithPlace<'tcx, P>: DisplayWithCtxt<Ctxt>,
    {
        let state = self.as_mut_ref();
        let replacements = state.graph.label_place(place, reason, labeller, ctxt);
        // If in a join we don't want to change capabilities because this will
        // essentially be handled by the join logic.
        // See 69_http_header_map.rs
        if reason != LabelPlaceReason::JoinOwnedReadAndWriteCapabilities {
            capabilities.retain(|p, _| !p.projects_indirection_from(place, ctxt));
        }
        let display = display_node_replacements(&replacements, ctxt, OutputMode::Normal);
        ApplyActionResult {
            changed: true,
            change_summary: display,
        }
    }

    fn label_lifetime_projections<'a, P, Ctxt: Copy>(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: Ctxt,
    ) -> bool
    where
        'tcx: 'a,
        EdgeKind: LabelEdgeLifetimeProjections<'tcx, Ctxt, P> + Eq + std::hash::Hash,
    {
        self.graph_mut()
            .label_lifetime_projections(predicate, label, ctxt)
    }

    fn remove<'a, P: Copy + Eq + std::hash::Hash, Ctxt: Copy, C>(
        &mut self,
        edge: &EdgeKind,
        capabilities: &mut impl PlaceCapabilitiesInterface<'tcx, C, P>,
        ctxt: Ctxt,
    ) -> bool
    where
        'tcx: 'a,
        EdgeKind: EdgeData<'tcx, Ctxt, P> + Eq + std::hash::Hash,
    {
        let state = self.as_mut_ref();
        let removed = state.graph.remove(edge).is_some();
        if removed {
            for node in edge.blocked_by_nodes(ctxt) {
                if !state.graph.contains(node, ctxt)
                    && let PcgNode::Place(MaybeLabelledPlace::Current(place)) = node
                {
                    let _ = capabilities.remove(place.into(), ctxt);
                }
            }
        }
        removed
    }

    fn apply_action<
        'a,
        Ctxt: DebugCtxt + Copy + OverrideRegionDebugString,
        P: PcgPlace<'tcx, Ctxt> + DisplayWithCtxt<Ctxt>,
        C: CapabilityLike,
    >(
        &mut self,
        action: BorrowPcgAction<'tcx, EdgeKind, P, VC>,
        capabilities: &mut impl PlaceCapabilitiesInterface<'tcx, C, P>,
        ctxt: Ctxt,
    ) -> Result<ApplyActionResult, PcgError>
    where
        'tcx: 'a,
        VC: ValidityConditionOps<Ctxt>,
        EdgeKind: EdgeData<'tcx, Ctxt, P>
            + LabelEdgePlaces<'tcx, Ctxt, P>
            + LabelEdgeLifetimeProjections<'tcx, Ctxt, P>
            + Eq
            + std::hash::Hash,
        MaybeRemotePlace<'tcx, P>: DisplayWithCtxt<Ctxt>,
    {
        let result = match action.kind {
            BorrowPcgActionKind::Restore(restore) => {
                let restore_place = restore.place();
                if let Some(cap) = capabilities.get(restore_place, ctxt) {
                    pcg_validity_assert!(cap.expect_concrete() < restore.capability())
                }
                if !capabilities.insert(restore_place, restore.capability(), ctxt) {
                    // panic!("Capability should have been updated")
                }
                if restore.capability() == CapabilityKind::Exclusive {
                    self.label_lifetime_projections(
                        &LabelNodePredicate::all_future_postfixes(restore_place),
                        None,
                        ctxt,
                    );
                }
                ApplyActionResult::changed_no_display()
            }
            BorrowPcgActionKind::Weaken(weaken) => {
                let weaken_place = weaken.place();
                pcg_validity_assert!(
                    capabilities
                        .get(weaken_place, ctxt)
                        .unwrap()
                        .expect_concrete()
                        == weaken.from,
                    [ctxt],
                    "Weakening from {:?} to {:?} is not valid",
                    capabilities
                        .get(weaken_place, ctxt)
                        .unwrap()
                        .expect_concrete(),
                    weaken.from
                );
                match weaken.to {
                    Some(to) => {
                        capabilities.insert(weaken_place, to, ctxt);
                    }
                    None => {
                        assert!(capabilities.remove(weaken_place, ctxt).is_some());
                    }
                }
                ApplyActionResult::changed_no_display()
            }
            BorrowPcgActionKind::LabelPlace(action) => self
                .label_place_and_update_related_capabilities(
                    action.place,
                    action.reason,
                    &SetLabel(action.location),
                    capabilities,
                    ctxt,
                ),
            BorrowPcgActionKind::RemoveEdge(edge) => {
                ApplyActionResult::from_changed(self.remove(&edge.value, capabilities, ctxt))
            }
            BorrowPcgActionKind::AddEdge { edge } => {
                ApplyActionResult::from_changed(self.graph_mut().insert(edge, ctxt))
            }
            BorrowPcgActionKind::LabelLifetimeProjection(action) => {
                let predicate = map_label_predicate(action.predicate());
                ApplyActionResult::from_changed(self.label_lifetime_projections(
                    &predicate,
                    action.label(),
                    ctxt,
                ))
            }
        };
        Ok(result)
    }
}

impl<'pcg, 'tcx: 'pcg> BorrowsStateLike<'tcx> for BorrowStateMutRef<'pcg, 'tcx> {
    fn as_mut_ref(&mut self) -> BorrowStateMutRef<'_, 'tcx> {
        BorrowStateMutRef::new(self.graph, self.validity_conditions)
    }

    fn graph(&self) -> &BorrowsGraph<'tcx> {
        self.graph
    }

    fn as_ref(&self) -> BorrowStateRef<'_, 'tcx> {
        BorrowStateRef::new(self.graph, self.validity_conditions)
    }
}

impl<'a, 'tcx, EdgeKind: Eq + std::hash::Hash, VC> BorrowsStateLike<'tcx, EdgeKind, VC>
    for BorrowsState<'a, 'tcx, EdgeKind, VC>
{
    fn as_mut_ref(&mut self) -> BorrowStateMutRef<'_, 'tcx, EdgeKind, VC> {
        BorrowStateMutRef::new(&mut self.graph, self.validity_conditions)
    }

    fn graph(&self) -> &BorrowsGraph<'tcx, EdgeKind, VC> {
        &self.graph
    }

    fn as_ref(&self) -> BorrowStateRef<'_, 'tcx, EdgeKind, VC> {
        BorrowStateRef::new(&self.graph, self.validity_conditions)
    }
}

impl<'pcg, 'tcx> From<&'pcg mut BorrowsState<'_, 'tcx>> for BorrowStateMutRef<'pcg, 'tcx> {
    fn from(borrows_state: &'pcg mut BorrowsState<'_, 'tcx>) -> Self {
        Self::new(&mut borrows_state.graph, borrows_state.validity_conditions)
    }
}

impl<'tcx> DebugLines<CompilerCtxt<'_, 'tcx>> for BorrowsState<'_, 'tcx> {
    fn debug_lines(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Vec<Cow<'static, str>> {
        self.graph.debug_lines(ctxt)
    }
}

impl<'a, 'tcx> HasValidityCheck<CompilerCtxt<'a, 'tcx>> for BorrowStateRef<'_, 'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> Result<(), String> {
        self.graph.check_validity(ctxt)
    }
}

impl<'a, 'tcx> HasValidityCheck<CompilerCtxt<'a, 'tcx>> for BorrowStateMutRef<'_, 'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> Result<(), String> {
        self.as_ref().check_validity(ctxt)
    }
}

impl<'a, 'tcx, EdgeKind: Eq + std::hash::Hash, VC> BorrowsState<'a, 'tcx, EdgeKind, VC> {
    fn introduce_initial_borrows<
        P,
        C: CapabilityLike,
        Ctxt: Copy + DebugCtxt + OverrideRegionDebugString,
    >(
        &mut self,
        local: mir::Local,
        capabilities: &mut impl PlaceCapabilitiesInterface<'tcx, C, P>,
        ctxt: Ctxt,
    ) where
        P: PlaceLike<'tcx, Ctxt> + DisplayWithCtxt<Ctxt>,
        EdgeKind: LabelEdgePlaces<'tcx, Ctxt, P>
            + LabelEdgeLifetimeProjections<'tcx, Ctxt, P>
            + EdgeData<'tcx, Ctxt, P>
            + From<BorrowFlowEdge<'tcx, P>>,
        RemotePlace: HasRegions<'tcx, Ctxt>,
        'tcx: 'a,
    {
        let arg_place: P = local.into();
        for region in arg_place.regions(ctxt) {
            let source_projection: LifetimeProjection<'tcx, RemotePlace> =
                LifetimeProjection::new(RemotePlace::new(local), region, None, ctxt)
                    .unwrap_or_else(|| {
                        panic!(
                            "Failed to create region for remote place (for {local:?}).
                                    It does not have region {region:?}",
                        );
                    });
            let source_projection: LifetimeProjection<'tcx, PcgLifetimeProjectionBase<'tcx, P>> =
                source_projection.rebase();
            let target_projection = LifetimeProjection::<'tcx, MaybeLabelledPlace<'tcx, P>>::new(
                MaybeLabelledPlace::Current(arg_place),
                region,
                None,
                ctxt,
            )
            .unwrap();
            assert!(
                self.apply_action(
                    BorrowPcgAction::add_edge(
                        BorrowPcgEdge::new(
                            BorrowFlowEdge::new(
                                source_projection,
                                target_projection,
                                BorrowFlowEdgeKind::InitialBorrows,
                            )
                            .into(),
                            ValidityConditions::new(),
                        ),
                        "Introduce initial borrows",
                    ),
                    capabilities,
                    ctxt,
                )
                .unwrap()
                .changed
            );
        }
    }

    pub(crate) fn start_block<
        P: PlaceLike<'tcx, Ctxt> + DisplayWithCtxt<Ctxt>,
        C: CapabilityLike,
        Ctxt: DebugCtxt + HasLocals + LocalTys<'tcx> + OverrideRegionDebugString,
    >(
        capabilities: &mut impl PlaceCapabilitiesInterface<'tcx, C, P>,
        ctxt: Ctxt,
    ) -> Self
    where
        EdgeKind: LabelEdgePlaces<'tcx, Ctxt, P>
            + LabelEdgeLifetimeProjections<'tcx, Ctxt, P>
            + EdgeData<'tcx, Ctxt, P>
            + From<BorrowFlowEdge<'tcx, P>>,
        'tcx: 'a,
    {
        let mut borrow = Self::default();
        for arg in ctxt.args_iter() {
            borrow.introduce_initial_borrows(arg, capabilities, ctxt);
        }
        borrow
    }
}

impl<'a, 'tcx> BorrowsState<'a, 'tcx> {
    pub fn graph(&self) -> &BorrowsGraph<'tcx> {
        &self.graph
    }

    pub(crate) fn join(
        &mut self,
        other: &Self,
        args: JoinBorrowsArgs<'_, 'a, 'tcx>,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) -> Result<(), PcgError> {
        self.graph
            .join(&other.graph, self.validity_conditions, args, ctxt)?;
        if let JoinValidityConditionsResult::Changed(new_validity_conditions) = self
            .validity_conditions
            .join_result(other.validity_conditions, ctxt.body())
        {
            self.validity_conditions = ctxt.arena.alloc(new_validity_conditions);
        }
        Ok(())
    }

    /// Remove all edges that are not valid for `path`, based on their validity
    /// conditions.
    pub fn filter_for_path(&mut self, path: &[BasicBlock], ctxt: CompilerCtxt<'_, 'tcx>) {
        self.graph.filter_for_path(path, ctxt);
    }

    pub(crate) fn edges_blocking<'slf, 'mir: 'slf>(
        &'slf self,
        node: BlockedNode<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> Vec<BorrowPcgEdgeRef<'tcx, 'slf>> {
        self.graph.edges_blocking(node, ctxt).collect()
    }

    pub fn nodes_blocking<'slf, 'mir: 'slf>(
        &'slf self,
        node: BlockedNode<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> HashSet<BlockingNode<'tcx>> {
        self.graph
            .edges_blocking(node, ctxt)
            .flat_map(|e| e.blocked_by_nodes(ctxt).collect::<Vec<_>>())
            .collect()
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn add_borrow<Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
        &mut self,
        blocked_place: Place<'tcx>,
        assigned_place: Place<'tcx>,
        kind: BorrowKind,
        location: Location,
        region: ty::Region<'tcx>,
        capabilities: &mut SymbolicPlaceCapabilities<'tcx>,
        ctxt: Ctxt,
    ) where
        'tcx: 'a,
    {
        assert!(
            assigned_place.ty(ctxt).ty.ref_mutability().is_some(),
            "{:?}:{:?} Assigned place {:?} is not a reference. Ty: {:?}",
            ctxt.body().source.def_id(),
            location,
            assigned_place,
            assigned_place.ty(ctxt).ty
        );
        let borrow_edge = BorrowEdge::new(
            blocked_place.into(),
            assigned_place.into(),
            kind,
            location,
            region,
            ctxt,
        );
        assert!(self.graph.insert(
            BorrowPcgEdge::new(
                BorrowPcgEdgeKind::Borrow(borrow_edge),
                self.validity_conditions.clone(),
            ),
            ctxt.ctxt()
        ));

        match kind {
            BorrowKind::Mut {
                kind: MutBorrowKind::Default | MutBorrowKind::ClosureCapture,
            } => {
                let _ = capabilities.remove(blocked_place, ctxt);
            }
            _ => {
                let blocked_place_capability = capabilities.get(blocked_place, ctxt);
                match blocked_place_capability.map(|c| c.expect_concrete()) {
                    Some(CapabilityKind::Exclusive) => {
                        assert!(capabilities.insert(blocked_place, CapabilityKind::Read, ctxt));
                    }
                    Some(CapabilityKind::Read) => {
                        // Do nothing, this just adds another shared borrow
                    }
                    other => {
                        // Shouldn't be None or Write, due to capability updates
                        // based on the TripleWalker analysis
                        pcg_validity_assert!(
                            false,
                            "{:?}: Unexpected capability for borrow blocked place {:?}: {:?}",
                            location,
                            blocked_place,
                            other
                        );
                    }
                }
            }
        }
    }
}

impl<'a, 'tcx, EdgeKind: PartialEq + Eq + std::hash::Hash> BorrowsState<'a, 'tcx, EdgeKind> {
    pub(crate) fn add_cfg_edge(
        &mut self,
        from: BasicBlock,
        to: BasicBlock,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) -> bool {
        pcg_validity_assert!(
            !ctxt.ctxt.is_back_edge(from, to),
            [ctxt],
            "Adding CFG edge from {from:?} to {to:?} is a back edge"
        );
        let pc = PathCondition::new(from, to);
        let mut validity_conditions = self.validity_conditions.clone();
        validity_conditions.insert(pc, ctxt.body());
        self.validity_conditions = ctxt.arena.alloc(validity_conditions);
        self.graph.add_path_condition(pc, ctxt.ctxt)
    }
}
