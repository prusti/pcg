//! The data structure representing the state of the Borrow PCG.

use std::borrow::Cow;

use crate::{
    HasSettings,
    borrow_pcg::{
        action::ApplyActionResult,
        borrow_pcg_edge::BlockingNode,
        edge_data::{LabelEdgeLifetimeProjections, LabelEdgePlaces, display_node_replacements},
        graph::join::JoinBorrowsArgs,
        region_projection::PcgLifetimeProjectionBase,
        validity_conditions::{
            JoinValidityConditionsResult, ValidityConditionOps, ValidityConditionsLike,
        },
    },
    pcg::PcgNodeWithPlace,
    utils::{
        DebugCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, HasLocals, PlaceLike,
        data_structures::HashSet,
        display::{DisplayWithCtxt, OutputMode},
        maybe_remote::MaybeRemotePlace,
    },
};

use super::{
    borrow_pcg_edge::{BlockedNode, BorrowPcgEdge, BorrowPcgEdgeRef},
    graph::BorrowsGraph,
    validity_conditions::{PathCondition, ValidityConditions},
};
use crate::{
    action::BorrowPcgAction,
    borrow_pcg::{
        action::{BorrowPcgActionKind, LabelPlaceReason},
        edge::{
            borrow_flow::{BorrowFlowEdge, BorrowFlowEdgeKind},
            kind::BorrowPcgEdgeKind,
        },
        edge_data::{EdgeData, LabelNodePredicate},
        has_pcs_elem::{PlaceLabeller, SetLabel},
        region_projection::{LifetimeProjection, LifetimeProjectionLabel},
    },
    pcg::{
        CapabilityKind, PcgNode, ctxt::AnalysisCtxt, place_capabilities::PlaceCapabilitiesInterface,
    },
    pcg_validity_assert,
    rustc_interface::middle::{
        mir::{self, BasicBlock},
        ty,
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
        LabelNodePredicate::PlaceEquals(place) => LabelNodePredicate::PlaceEquals(*place),
        LabelNodePredicate::PlaceIsPostfixOf(place) => LabelNodePredicate::PlaceIsPostfixOf(*place),
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

/// Ends the freeze of `place` while `to` stay frozen: the read unpacking of
/// `place` becomes an exclusive one, except for `to` and their unpackings.
/// Returns the places that get E.
fn end_freeze<'tcx, Ctxt: Copy, P: PlaceLike<'tcx, Ctxt>>(
    place: P,
    to: &[P],
    capabilities: &mut impl PlaceCapabilitiesInterface<'tcx, CapabilityKind, P>,
    ctxt: Ctxt,
) -> Vec<P> {
    let holders = std::iter::once(place)
        .chain(
            capabilities
                .capabilities_for_strict_postfixes_of(place)
                .map(|(p, _)| p),
        )
        .collect::<Vec<_>>();
    let mut exclusive = vec![];
    for &p in &holders {
        if to.iter().any(|t| t.is_prefix_of(p)) {
            continue;
        }
        let unpacked = holders.iter().any(|h| p.is_strict_prefix_of(*h));
        match exclusively_unpacked_capability(p, unpacked, ctxt) {
            Some(cap) => {
                capabilities.insert(p, cap, ctxt);
                if cap == CapabilityKind::Exclusive {
                    exclusive.push(p);
                }
            }
            None => {
                let _ = capabilities.remove(p, ctxt);
            }
        }
    }
    exclusive
}

/// The capability of `place` in an exclusive unpacking: an `unpacked` place
/// keeps none (`e` for a mutable reference, R for a dereferenced shared
/// reference), and a leaf has E. Places behind a shared reference keep R.
fn exclusively_unpacked_capability<'tcx, Ctxt: Copy, P: PlaceLike<'tcx, Ctxt>>(
    place: P,
    unpacked: bool,
    ctxt: Ctxt,
) -> Option<CapabilityKind> {
    let behind_shared_ref = place
        .iter_projections(ctxt)
        .into_iter()
        .any(|(base, elem)| {
            matches!(elem, mir::ProjectionElem::Deref)
                && matches!(
                    base.rust_ty(ctxt).kind(),
                    ty::Ref(_, _, ty::Mutability::Not)
                )
        });
    if behind_shared_ref {
        return Some(CapabilityKind::Read);
    }
    if !unpacked {
        return Some(CapabilityKind::Exclusive);
    }
    match place.rust_ty(ctxt).kind() {
        ty::Ref(_, _, ty::Mutability::Mut) => Some(CapabilityKind::ShallowExclusive),
        ty::Ref(_, _, ty::Mutability::Not) => Some(CapabilityKind::Read),
        _ => None,
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

impl<EdgeKind: PartialEq + Eq + std::hash::Hash, VC: ValidityConditionsLike> Default
    for BorrowsState<'_, '_, EdgeKind, VC>
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
    pub(crate) graph: &'pcg BorrowsGraph<'tcx, EdgeKind, VC>,
    #[allow(unused)]
    pub(crate) validity_conditions: &'pcg VC,
}

impl<'pcg, 'tcx, EdgeKind: std::hash::Hash + Eq, VC> BorrowStateRef<'pcg, 'tcx, EdgeKind, VC> {
    pub(crate) fn new(
        graph: &'pcg BorrowsGraph<'tcx, EdgeKind, VC>,
        validity_conditions: &'pcg VC,
    ) -> Self {
        Self {
            graph,
            validity_conditions,
        }
    }
}

impl<EdgeKind, VC> Clone for BorrowStateRef<'_, '_, EdgeKind, VC> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<EdgeKind, VC> Copy for BorrowStateRef<'_, '_, EdgeKind, VC> {}

pub(crate) trait BorrowsStateLike<'tcx, EdgeKind = BorrowPcgEdgeKind<'tcx>, VC = ValidityConditions>
{
    fn as_mut_ref(&mut self) -> BorrowStateMutRef<'_, 'tcx, EdgeKind, VC>;
    fn as_ref(&self) -> BorrowStateRef<'_, 'tcx, EdgeKind, VC>;

    fn graph_mut(&mut self) -> &mut BorrowsGraph<'tcx, EdgeKind, VC> {
        self.as_mut_ref().graph
    }
    fn graph(&self) -> &BorrowsGraph<'tcx, EdgeKind, VC>;

    fn label_place_and_update_related_capabilities<
        'a,
        P: PlaceLike<'tcx, Ctxt> + DisplayWithCtxt<Ctxt>,
        Ctxt: Copy + HasCompilerCtxt<'a, 'tcx>,
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
        VC: ValidityConditionOps<Ctxt>,
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
        VC: ValidityConditionOps<Ctxt>,
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
                    let _ = capabilities.remove(place, ctxt);
                }
            }
        }
        removed
    }

    fn apply_action<
        'a,
        Ctxt: DebugCtxt + HasCompilerCtxt<'a, 'tcx> + HasSettings<'a>,
        P: PlaceLike<'tcx, Ctxt> + DisplayWithCtxt<Ctxt>,
    >(
        &mut self,
        action: BorrowPcgAction<'tcx, EdgeKind, P, VC>,
        capabilities: &mut impl PlaceCapabilitiesInterface<'tcx, CapabilityKind, P>,
        ctxt: Ctxt,
    ) -> ApplyActionResult
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
        match action.kind {
            BorrowPcgActionKind::Weaken(weaken) => {
                let weaken_place = weaken.place();
                pcg_validity_assert!(
                    capabilities.get(weaken_place, ctxt).unwrap() == weaken.from,
                    [ctxt],
                    "Weakening from {:?} to {:?} is not valid",
                    capabilities.get(weaken_place, ctxt).unwrap(),
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
            BorrowPcgActionKind::Freeze { place } => {
                pcg_validity_assert!(
                    matches!(
                        capabilities.get(place, ctxt),
                        Some(CapabilityKind::Exclusive) | None
                    ),
                    [ctxt],
                    "Freezing {} with capability {:?}",
                    place.display_string(ctxt),
                    capabilities.get(place, ctxt)
                );
                capabilities.insert(place, CapabilityKind::Read, ctxt);
                for (p, cap) in capabilities
                    .capabilities_for_strict_postfixes_of(place)
                    .collect::<Vec<_>>()
                {
                    pcg_validity_assert!(
                        !cap.is_write(),
                        [ctxt],
                        "Freezing {} with uninitialised {}",
                        place.display_string(ctxt),
                        p.display_string(ctxt)
                    );
                    capabilities.insert(p, CapabilityKind::Read, ctxt);
                }
                ApplyActionResult::changed_no_display()
            }
            BorrowPcgActionKind::Unfreeze { place } => {
                pcg_validity_assert!(
                    capabilities.get(place, ctxt) == Some(CapabilityKind::Read),
                    [ctxt],
                    "Unfreezing {} with capability {:?}",
                    place.display_string(ctxt),
                    capabilities.get(place, ctxt)
                );
                for p in end_freeze(place, &[], capabilities, ctxt) {
                    self.label_lifetime_projections(
                        &LabelNodePredicate::all_future_postfixes(p),
                        None,
                        ctxt,
                    );
                }
                ApplyActionResult::changed_no_display()
            }
            BorrowPcgActionKind::Refreeze { place, to } => {
                pcg_validity_assert!(
                    capabilities.get(place, ctxt) == Some(CapabilityKind::Read),
                    [ctxt],
                    "Refreezing {} with capability {:?}",
                    place.display_string(ctxt),
                    capabilities.get(place, ctxt)
                );
                for p in end_freeze(place, &to, capabilities, ctxt) {
                    self.label_lifetime_projections(
                        &LabelNodePredicate::all_future_postfixes(p),
                        None,
                        ctxt,
                    );
                }
                ApplyActionResult::changed_no_display()
            }
            BorrowPcgActionKind::ActivateTwoPhaseBorrow { borrow } => {
                let place = borrow.blocked_place.place();
                pcg_validity_assert!(
                    capabilities.get(place, ctxt) == Some(CapabilityKind::Read),
                    [ctxt],
                    "Activating a two-phase borrow of {} with capability {:?}",
                    place.display_string(ctxt),
                    capabilities.get(place, ctxt)
                );
                let _ = capabilities.remove(place, ctxt);
                ApplyActionResult::changed_no_display()
            }
            BorrowPcgActionKind::LabelPlace(action) => {
                let result = self.label_place_and_update_related_capabilities(
                    action.place,
                    action.reason,
                    &SetLabel(action.location),
                    capabilities,
                    ctxt,
                );
                for (place, cap) in action.capabilities {
                    capabilities.insert(place, cap, ctxt);
                }
                result
            }
            BorrowPcgActionKind::RemoveEdge { edge, regained } => {
                let removed = self.remove(&edge.value, capabilities, ctxt);
                for (place, cap) in regained {
                    if let Some(current) = capabilities.get(place, ctxt) {
                        pcg_validity_assert!(current < cap);
                    }
                    capabilities.insert(place, cap, ctxt);
                    if cap == CapabilityKind::Exclusive {
                        self.label_lifetime_projections(
                            &LabelNodePredicate::all_future_postfixes(place),
                            None,
                            ctxt,
                        );
                    }
                }
                ApplyActionResult::from_changed(removed)
            }
            BorrowPcgActionKind::AddEdge {
                edge,
                capabilities: set,
            } => {
                let mut changed = self.graph_mut().insert(edge, ctxt);
                for (place, cap) in set {
                    changed |= match cap {
                        Some(cap) => capabilities.insert(place, cap, ctxt),
                        None => capabilities.remove(place, ctxt).is_some(),
                    };
                }
                ApplyActionResult::from_changed(changed)
            }
            BorrowPcgActionKind::LabelLifetimeProjection(action) => {
                let predicate = map_label_predicate(action.predicate());
                ApplyActionResult::from_changed(self.label_lifetime_projections(
                    &predicate,
                    action.label(),
                    ctxt,
                ))
            }
        }
    }

    fn edges_blocking<'slf, Ctxt: Copy + DebugCtxt>(
        &'slf self,
        node: BlockedNode<'tcx>,
        ctxt: Ctxt,
    ) -> impl Iterator<Item = BorrowPcgEdgeRef<'tcx, 'slf, EdgeKind, VC>>
    where
        EdgeKind: EdgeData<'tcx, Ctxt, Place<'tcx>> + std::hash::Hash + Eq + 'slf,
        VC: 'slf,
        'tcx: 'slf,
    {
        self.graph().edges_blocking(node, ctxt)
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

impl<'tcx, EdgeKind: Eq + std::hash::Hash, VC> BorrowsStateLike<'tcx, EdgeKind, VC>
    for BorrowsState<'_, 'tcx, EdgeKind, VC>
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

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx> + DebugCtxt> DebugLines<Ctxt>
    for BorrowsState<'_, 'tcx>
{
    fn debug_lines(&self, ctxt: Ctxt) -> Vec<Cow<'static, str>> {
        self.graph.debug_lines(ctxt)
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx> + DebugCtxt> HasValidityCheck<Ctxt>
    for BorrowStateRef<'_, 'tcx>
{
    fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
        self.graph.check_validity(ctxt)
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx> + DebugCtxt> HasValidityCheck<Ctxt>
    for BorrowStateMutRef<'_, 'tcx>
{
    fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
        self.as_ref().check_validity(ctxt)
    }
}

impl<EdgeKind: Eq + std::hash::Hash, VC> BorrowsState<'_, '_, EdgeKind, VC> {}

impl<'a, 'tcx> BorrowsState<'a, 'tcx, BorrowPcgEdgeKind<'tcx>, ValidityConditions> {
    fn introduce_initial_borrows(
        &mut self,
        local: mir::Local,
        capabilities: &mut impl PlaceCapabilitiesInterface<'tcx, CapabilityKind, Place<'tcx>>,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) {
        let arg_place: Place<'tcx> = local.into();
        for region in arg_place.regions(ctxt) {
            let source_projection: LifetimeProjection<'tcx, RemotePlace> =
                LifetimeProjection::new(RemotePlace::new(local), region, None, ctxt)
                    .unwrap_or_else(|| {
                        panic!(
                            "Failed to create region for remote place (for {local:?}).
                                    It does not have region {region:?}",
                        );
                    });
            let source_projection: LifetimeProjection<'tcx, PcgLifetimeProjectionBase<'tcx>> =
                source_projection.rebase();
            let target_projection = LifetimeProjection::<'tcx, MaybeLabelledPlace<'tcx>>::new(
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
                    ctxt
                )
                .changed
            );
        }
    }

    pub(crate) fn start_block(
        capabilities: &mut impl PlaceCapabilitiesInterface<'tcx, CapabilityKind, Place<'tcx>>,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) -> Self {
        let mut borrow = Self::default();
        for arg in ctxt.args_iter() {
            borrow.introduce_initial_borrows(arg, capabilities, ctxt);
        }
        borrow
    }
}

impl<'a, 'tcx> BorrowsState<'a, 'tcx> {
    #[must_use]
    pub fn graph(&self) -> &BorrowsGraph<'tcx> {
        &self.graph
    }

    /// The branch choices taken on every path reaching this state.
    #[must_use]
    pub fn validity_conditions(&self) -> &ValidityConditions {
        self.validity_conditions
    }

    pub(crate) fn merge(&mut self, other: &Self, ctxt: AnalysisCtxt<'a, 'tcx>) {
        self.graph.merge(&other.graph, ctxt);
        if let JoinValidityConditionsResult::Changed(new_validity_conditions) = self
            .validity_conditions
            .join_result(other.validity_conditions, ctxt.body())
        {
            self.validity_conditions = ctxt.arena.alloc(new_validity_conditions);
        }
    }

    pub(crate) fn finish_join(
        &mut self,
        args: JoinBorrowsArgs<'_, 'a, 'tcx>,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) {
        self.graph.finish_join(self.validity_conditions, args, ctxt);
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

    #[must_use]
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
