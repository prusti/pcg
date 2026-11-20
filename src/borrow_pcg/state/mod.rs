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
    pcg::{PcgNodeWithPlace, place_capabilities::PlaceCapabilitiesReader},
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
    action::{BorrowPcgAction, CapabilityChanges},
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
        CapabilityKind, PcgNode, ctxt::AnalysisCtxt, meet,
        place_capabilities::PlaceCapabilitiesInterface, value::StepKind,
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

/// The capability changes of ending the freeze of `place` while `to` stay
/// frozen: the read unpacking of `place` becomes an exclusive one, except for
/// `to` and their unpackings and for the read copies `dropped`, which are
/// given up. Each leaf gets back the capability suspended for it or for the
/// frozen place it is a read copy of.
fn end_freeze<'tcx, Ctxt: Copy, P: PlaceLike<'tcx, Ctxt>>(
    place: P,
    to: &[P],
    dropped: &[P],
    capabilities: &impl PlaceCapabilitiesReader<'tcx, CapabilityKind, P>,
    ctxt: Ctxt,
) -> CapabilityChanges<P> {
    let holders = std::iter::once(place)
        .chain(
            capabilities
                .capabilities_for_strict_postfixes_of(place)
                .map(|(p, _)| p),
        )
        .filter(|p| !dropped.contains(p))
        .collect::<Vec<_>>();
    let mut changes = CapabilityChanges::default();
    for &p in &holders {
        if to.iter().any(|t| t.is_prefix_of(p)) {
            continue;
        }
        let unpacked = holders.iter().any(|h| p.is_strict_prefix_of(*h));
        changes.set(
            p,
            exclusively_unpacked_capability(
                p,
                unpacked,
                suspended_for(place, p, capabilities),
                ctxt,
            ),
        );
    }
    changes
}

/// Keeps the records of the freeze of `place`, which `changes` end, only for
/// what stays frozen: `to` and the shared references whose referents stay
/// unpacked. The freeze moves to them with what it suspends.
fn keep_records_of_still_frozen<'tcx, Ctxt: Copy, P: PlaceLike<'tcx, Ctxt>>(
    place: P,
    to: &[P],
    changes: &CapabilityChanges<P>,
    capabilities: &mut impl PlaceCapabilitiesInterface<'tcx, CapabilityKind, P>,
    ctxt: Ctxt,
) {
    let still_frozen = to
        .iter()
        .copied()
        .chain(
            changes
                .iter()
                .filter(|(p, cap)| {
                    *cap == Some(CapabilityKind::Read) && !is_behind_shared_ref(*p, ctxt)
                })
                .map(|(p, _)| p),
        )
        .collect::<Vec<_>>();
    for &t in &still_frozen {
        if capabilities.suspended(t).is_none()
            && let Some(suspended) = suspended_for(place, t, capabilities)
        {
            capabilities.suspend(t, suspended);
        }
    }
    capabilities.retain_suspended(|p, _| {
        !place.is_prefix_of(p) || still_frozen.iter().any(|t| t.is_prefix_of(p))
    });
}

/// The capability suspended for `p` by the freeze of `frozen`: the one
/// suspended for `p` or for the closest place between `frozen` and `p`.
fn suspended_for<'tcx, Ctxt: Copy, P: PlaceLike<'tcx, Ctxt>>(
    frozen: P,
    p: P,
    capabilities: &impl PlaceCapabilitiesReader<'tcx, CapabilityKind, P>,
) -> Option<CapabilityKind> {
    capabilities
        .iter_suspended()
        .filter(|(q, _)| frozen.is_prefix_of(*q) && q.is_prefix_of(p))
        .reduce(|a, b| if a.0.is_strict_prefix_of(b.0) { b } else { a })
        .map(|(_, capability)| capability)
}

/// The record `place` gets by packing the records in its value into it; see
/// [`packed`]. Returns it with the places whose records it packs, `place`
/// aside.
pub(crate) fn packed_record<
    'a,
    'tcx: 'a,
    Ctxt: HasCompilerCtxt<'a, 'tcx>,
    P: PlaceLike<'tcx, Ctxt>,
>(
    place: P,
    capabilities: &impl PlaceCapabilitiesReader<'tcx, CapabilityKind, P>,
    ctxt: Ctxt,
) -> (Option<CapabilityKind>, Vec<P>) {
    packed(
        place,
        &capabilities.iter_suspended().collect::<Vec<_>>(),
        ctxt,
    )
}

/// What `place` gets when the capabilities (or records) `entries` in its
/// value are packed into it, the inverse of unpacking: the meet of the
/// entries stored in it, where a mutable reference with e whose referent
/// packs to E counts as E. What lies behind a shared reference or a raw
/// pointer adds nothing. Returns it with the places whose entries it packs,
/// `place` aside.
pub(crate) fn packed<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>, P: PlaceLike<'tcx, Ctxt>>(
    place: P,
    entries: &[(P, CapabilityKind)],
    ctxt: Ctxt,
) -> (Option<CapabilityKind>, Vec<P>) {
    let mut packed_capability = None;
    let mut parts = vec![];
    for &(p, entry) in entries.iter().filter(|(p, _)| place.in_storage(*p, ctxt)) {
        let entry = if entry == CapabilityKind::ShallowExclusive
            && let ty::Ref(_, _, ty::Mutability::Mut) = p.rust_ty(ctxt).kind()
            && let Ok(referent) = p.project_deeper(mir::ProjectionElem::Deref, ctxt)
            && let (Some(CapabilityKind::Exclusive), referent_parts) =
                packed(referent, entries, ctxt)
        {
            parts.extend(referent_parts);
            if entries.iter().any(|(q, _)| *q == referent) {
                parts.push(referent);
            }
            CapabilityKind::Exclusive
        } else {
            entry
        };
        if p != place {
            parts.push(p);
        }
        packed_capability = Some(packed_capability.map_or(entry, |acc| meet(acc, entry)));
    }
    (packed_capability, parts)
}

/// Whether `p` is part of the current value of `place` that labelling it
/// for `reason` labels: all of it for a detach, otherwise what lies behind
/// a reference or raw pointer in it (the rest is overwritten in place). A
/// written place behind a reference is unpacked in the borrow PCG, and the
/// label gives that unpacking to the old value: all its parts are labelled.
fn is_labelled<'tcx, Ctxt: Copy, P: PlaceLike<'tcx, Ctxt>>(
    place: P,
    reason: LabelPlaceReason,
    p: P,
    ctxt: Ctxt,
) -> bool {
    let local: P = place.local().into();
    match reason {
        // The referent and its read copies move to the label.
        LabelPlaceReason::Detach => place.is_prefix_of(p),
        LabelPlaceReason::Write if !local.in_storage(place, ctxt) => place.is_strict_prefix_of(p),
        _ => place.is_prefix_of(p) && !place.in_storage(p, ctxt),
    }
}

/// The capability changes of labelling the current value of `place`: the
/// current places reached from `place` through a dereference lose their
/// capabilities; a detached referent loses them with all its postfixes. A
/// written place behind a reference whose parts went with the old value
/// holds nothing of its own but is about to be written: it gets W.
pub(crate) fn label_place_changes<'tcx, Ctxt: Copy, P: PlaceLike<'tcx, Ctxt>>(
    place: P,
    reason: LabelPlaceReason,
    capabilities: &impl PlaceCapabilitiesReader<'tcx, CapabilityKind, P>,
    ctxt: Ctxt,
) -> CapabilityChanges<P> {
    let mut changes: CapabilityChanges<P> = capabilities
        .iter()
        .filter(|(p, _)| is_labelled(place, reason, *p, ctxt))
        .map(|(p, _)| (p, None))
        .collect::<Vec<_>>()
        .into();
    let local: P = place.local().into();
    if reason == LabelPlaceReason::Write
        && !local.in_storage(place, ctxt)
        && capabilities.get(place, ctxt).is_none()
        && capabilities
            .iter()
            .any(|(p, _)| place.is_strict_prefix_of(p))
    {
        changes.set(place, Some(CapabilityKind::Write));
    }
    changes
}

fn is_behind_shared_ref<'tcx, Ctxt: Copy, P: PlaceLike<'tcx, Ctxt>>(place: P, ctxt: Ctxt) -> bool {
    place
        .steps_from(place.local().into(), ctxt)
        .is_some_and(|steps| steps.contains(&StepKind::SharedDeref))
}

/// The capability of `place` in an exclusive unpacking: an `unpacked` place
/// keeps what unpacking E leaves it (see [`StepKind::kept`]; a raw pointer
/// keeps its own, `leaf`), and a leaf has `leaf`. Places behind a shared
/// reference keep R.
fn exclusively_unpacked_capability<'tcx, Ctxt: Copy, P: PlaceLike<'tcx, Ctxt>>(
    place: P,
    unpacked: bool,
    leaf: Option<CapabilityKind>,
    ctxt: Ctxt,
) -> Option<CapabilityKind> {
    if is_behind_shared_ref(place, ctxt) {
        return Some(CapabilityKind::Read);
    }
    if !unpacked {
        return leaf;
    }
    let ty = place.rust_ty(ctxt);
    let step = if ty.is_ref() || ty.is_raw_ptr() || ty.is_box() {
        place.step_kind(mir::ProjectionElem::Deref, ctxt)
    } else {
        StepKind::Owned
    };
    match step {
        StepKind::RawDeref => leaf,
        step => step.kept(CapabilityKind::Exclusive),
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

    /// Labels the current value of `place` in the graph only; applying a
    /// `LabelPlace` action also applies [`label_place_changes`].
    fn label_place<
        'a,
        P: PlaceLike<'tcx, Ctxt> + DisplayWithCtxt<Ctxt>,
        Ctxt: Copy + HasCompilerCtxt<'a, 'tcx>,
    >(
        &mut self,
        place: P,
        reason: LabelPlaceReason,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
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

    /// Applies `action` and records its capability changes in it: the changes
    /// its kind determines, then the ones given with it.
    fn apply_action<
        'a,
        Ctxt: DebugCtxt + HasCompilerCtxt<'a, 'tcx> + HasSettings<'a>,
        P: PlaceLike<'tcx, Ctxt> + DisplayWithCtxt<Ctxt>,
    >(
        &mut self,
        action: &mut BorrowPcgAction<'tcx, EdgeKind, P, VC>,
        capabilities: &mut impl PlaceCapabilitiesInterface<'tcx, CapabilityKind, P>,
        ctxt: Ctxt,
    ) -> ApplyActionResult
    where
        'tcx: 'a,
        VC: ValidityConditionOps<Ctxt> + Clone,
        EdgeKind: EdgeData<'tcx, Ctxt, P>
            + LabelEdgePlaces<'tcx, Ctxt, P>
            + LabelEdgeLifetimeProjections<'tcx, Ctxt, P>
            + Eq
            + std::hash::Hash
            + Clone,
        MaybeRemotePlace<'tcx, P>: DisplayWithCtxt<Ctxt>,
    {
        let mut changes = CapabilityChanges::default();
        let mut result = ApplyActionResult::changed_no_display();
        // The read copies that the changes given with an `Unfreeze` or a
        // `Refreeze` give up.
        let dropped = action
            .capabilities
            .iter()
            .filter_map(|(p, cap)| cap.is_none().then_some(p))
            .collect::<Vec<_>>();
        match &action.kind {
            BorrowPcgActionKind::Weaken(weaken) => {
                let current = capabilities.get(weaken.place, ctxt);
                pcg_validity_assert!(
                    current == Some(weaken.from) && weaken.from > weaken.to,
                    [ctxt],
                    "Weakening {} with capability {:?} from {:?} to {:?}",
                    weaken.place.display_string(ctxt),
                    current,
                    weaken.from,
                    weaken.to
                );
                changes.set(weaken.place, Some(weaken.to));
            }
            BorrowPcgActionKind::Freeze { place } => {
                pcg_validity_assert!(
                    matches!(
                        capabilities.get(*place, ctxt),
                        Some(CapabilityKind::Exclusive | CapabilityKind::ShallowExclusive) | None
                    ),
                    [ctxt],
                    "Freezing {} with capability {:?}",
                    place.display_string(ctxt),
                    capabilities.get(*place, ctxt)
                );
                // An unpacked place suspends what its parts hold packed
                // together (see `packed`), a frozen part what its freeze
                // suspends; a place stored in a part that holds a capability
                // counts through that part.
                let below = capabilities
                    .capabilities_for_strict_postfixes_of(*place)
                    .collect::<Vec<_>>();
                let holders = below
                    .iter()
                    .filter(|(p, _)| {
                        !below
                            .iter()
                            .any(|(q, _)| q.is_strict_prefix_of(*p) && q.in_storage(*p, ctxt))
                    })
                    .map(|&(p, cap)| (p, capabilities.suspended(p).unwrap_or(cap)))
                    .collect::<Vec<_>>();
                let (packed, _) = packed(*place, &holders, ctxt);
                let suspended =
                    std::iter::once((*place, capabilities.get(*place, ctxt).or(packed)))
                        .chain(
                            capabilities
                                .capabilities_for_strict_postfixes_of(*place)
                                .map(|(p, cap)| (p, Some(cap))),
                        )
                        .filter_map(|(p, cap)| Some((p, cap.filter(|cap| !cap.is_read())?)))
                        .collect::<Vec<_>>();
                for (p, cap) in suspended {
                    capabilities.suspend(p, cap);
                }
                changes.set(*place, Some(CapabilityKind::Read));
                for (p, cap) in capabilities.capabilities_for_strict_postfixes_of(*place) {
                    pcg_validity_assert!(
                        !cap.is_write(),
                        [ctxt],
                        "Freezing {} with uninitialised {}",
                        place.display_string(ctxt),
                        p.display_string(ctxt)
                    );
                    changes.set(p, Some(CapabilityKind::Read));
                }
            }
            BorrowPcgActionKind::Unfreeze { place } => {
                pcg_validity_assert!(
                    capabilities.get(*place, ctxt) == Some(CapabilityKind::Read),
                    [ctxt],
                    "Unfreezing {} with capability {:?}",
                    place.display_string(ctxt),
                    capabilities.get(*place, ctxt)
                );
                changes = end_freeze(*place, &[], &dropped, capabilities, ctxt);
                keep_records_of_still_frozen(*place, &[], &changes, capabilities, ctxt);
            }
            BorrowPcgActionKind::Refreeze { place, to } => {
                pcg_validity_assert!(
                    capabilities.get(*place, ctxt) == Some(CapabilityKind::Read),
                    [ctxt],
                    "Refreezing {} with capability {:?}",
                    place.display_string(ctxt),
                    capabilities.get(*place, ctxt)
                );
                changes = end_freeze(*place, to, &dropped, capabilities, ctxt);
                keep_records_of_still_frozen(*place, to, &changes, capabilities, ctxt);
            }
            // A reservation of a labelled place takes no capability.
            BorrowPcgActionKind::ActivateTwoPhaseBorrow { borrow }
                if !matches!(borrow.blocked_place, MaybeLabelledPlace::Current(_)) => {}
            BorrowPcgActionKind::ActivateTwoPhaseBorrow { borrow } => {
                let place = borrow.blocked_place.place();
                let frozen = capabilities.get(place, ctxt) == Some(CapabilityKind::Read)
                    && capabilities.suspended(place).is_some()
                    && !capabilities
                        .iter()
                        .any(|(p, cap)| p.is_strict_prefix_of(place) && cap.is_read());
                pcg_validity_assert!(
                    frozen,
                    [ctxt],
                    "Activating a two-phase borrow of {}, which is not frozen (capability {:?})",
                    place.display_string(ctxt),
                    capabilities.get(place, ctxt)
                );
                changes.set(place, None);
            }
            BorrowPcgActionKind::LabelPlace(label) => {
                changes = label_place_changes(label.place, label.reason, capabilities, ctxt);
                capabilities
                    .retain_suspended(|p, _| !is_labelled(label.place, label.reason, p, ctxt));
                result =
                    self.label_place(label.place, label.reason, &SetLabel(label.location), ctxt);
            }
            BorrowPcgActionKind::RemoveEdge(edge) => {
                let graph = self.graph_mut();
                let removed = graph.remove(&edge.value).is_some();
                if removed {
                    for node in edge.value.blocked_by_nodes(ctxt) {
                        if !graph.contains(node, ctxt)
                            && let PcgNode::Place(MaybeLabelledPlace::Current(place)) = node
                        {
                            if capabilities.get(place, ctxt).is_some() {
                                changes.set(place, None);
                            }
                            capabilities.resume(place);
                        }
                    }
                }
                result = ApplyActionResult::from_changed(removed);
            }
            BorrowPcgActionKind::AddEdge { edge } => {
                // A loan suspends the capabilities it takes; an unpacking
                // moves them to its expansion.
                for (place, capability) in action.capabilities.iter() {
                    if capability.is_none()
                        && let Some(lent) = capabilities.get(place, ctxt)
                        && !edge.value.blocked_by_nodes(ctxt).any(|node| {
                            matches!(
                                node,
                                PcgNode::Place(MaybeLabelledPlace::Current(p))
                                    if place.is_strict_prefix_of(p)
                            )
                        })
                    {
                        capabilities.suspend(place, lent);
                    }
                }
                result =
                    ApplyActionResult::from_changed(self.graph_mut().insert(edge.clone(), ctxt));
            }
            BorrowPcgActionKind::Lend { place, edge } => {
                // What `place` lends is recorded for it: a frozen place lends
                // what its freeze suspends, with its read copies; a place
                // behind a reference held with E is lent through it with its
                // share, and the reference keeps what the dereference leaves
                // it (e for a mutable one).
                let reference = capabilities.iter().find_map(|(reference, cap)| {
                    if cap != CapabilityKind::Exclusive || !reference.is_strict_prefix_of(*place) {
                        return None;
                    }
                    let deref = place
                        .steps_from(reference, ctxt)?
                        .into_iter()
                        .find(|step| !step.is_storage())?;
                    matches!(deref, StepKind::MutDeref | StepKind::SharedDeref)
                        .then_some((reference, deref))
                });
                if let Some((reference, deref)) = reference {
                    changes.set(reference, deref.kept(CapabilityKind::Exclusive));
                }
                let held = capabilities.get(*place, ctxt);
                let suspended = capabilities.suspended(*place);
                if held == Some(CapabilityKind::Read) && suspended.is_some() {
                    for (p, _) in capabilities.capabilities_for_strict_postfixes_of(*place) {
                        changes.set(p, None);
                    }
                }
                if let Some(lent) = suspended.or(held).or(reference.and_then(|(reference, _)| {
                    reference.share_at(CapabilityKind::Exclusive, *place, ctxt)
                })) {
                    capabilities.suspend(*place, lent);
                }
                self.graph_mut().insert(edge.clone(), ctxt);
                changes.set(*place, None);
            }
            BorrowPcgActionKind::UnpackSuspended { place, parts } => {
                let suspended = capabilities.resume(*place);
                pcg_validity_assert!(
                    suspended.is_some(),
                    [ctxt],
                    "Unpacking the suspended capability of {}, which has none",
                    place.display_string(ctxt)
                );
                if let Some(suspended) = suspended {
                    for &part in parts {
                        // Across a dereference the base keeps its record (the
                        // capability it gets back once the referent is packed
                        // again), a mutable reference e of E; the referent
                        // gets its share, if any. A base whose record gives
                        // its stored part nothing (a Box without contents)
                        // keeps it.
                        let Some(&[step]) = part.steps_from(*place, ctxt).as_deref() else {
                            pcg_validity_assert!(
                                false,
                                [ctxt],
                                "Unpacking the suspended capability of {} to {}, which is not one \
                                 level below it",
                                place.display_string(ctxt),
                                part.display_string(ctxt)
                            );
                            continue;
                        };
                        let share = step.share(suspended);
                        if !step.is_storage() || share.is_none() {
                            let kept = match step {
                                StepKind::MutDeref => step.kept(suspended),
                                _ => None,
                            };
                            capabilities.suspend(*place, kept.unwrap_or(suspended));
                        }
                        let Some(share) = share else {
                            continue;
                        };
                        // A part that records less gets back at most that.
                        let share = capabilities
                            .suspended(part)
                            .map_or(share, |own| meet(own, share));
                        capabilities.suspend(part, share);
                    }
                }
            }
            BorrowPcgActionKind::PackSuspended { place } => {
                let (packed, parts) = packed_record(*place, capabilities, ctxt);
                for part in parts {
                    capabilities.resume(part);
                }
                if let Some(packed) = packed {
                    capabilities.resume(*place);
                    capabilities.suspend(*place, packed);
                }
            }
            BorrowPcgActionKind::WeakenSuspended { place, from, to } => {
                let current = capabilities.resume(*place);
                pcg_validity_assert!(
                    current == Some(*from)
                        && to.is_none_or(|to| to != *from && meet(*from, to) == to),
                    [ctxt],
                    "Weakening the suspended {:?} of {} from {:?} to {:?}",
                    current,
                    place.display_string(ctxt),
                    from,
                    to
                );
                if let Some(to) = to {
                    capabilities.suspend(*place, *to);
                }
            }
            BorrowPcgActionKind::LabelLifetimeProjection(label) => {
                let predicate = map_label_predicate(label.predicate());
                result = ApplyActionResult::from_changed(self.label_lifetime_projections(
                    &predicate,
                    label.label(),
                    ctxt,
                ));
            }
        }
        changes.extend(&action.capabilities);
        result.changed |= if matches!(
            action.kind,
            BorrowPcgActionKind::Unfreeze { .. } | BorrowPcgActionKind::Refreeze { .. }
        ) {
            self.regain(&changes, capabilities, ctxt)
        } else {
            changes.apply(capabilities, ctxt)
        };
        action.capabilities = changes;
        result
    }

    /// Applies `changes`, which give capabilities back, ending the suspension
    /// of the places that get one above R (a place that gets R stays frozen);
    /// the places that get E back are accessed exclusively again.
    fn regain<'a, Ctxt: Copy, P: Copy + Eq + std::hash::Hash>(
        &mut self,
        changes: &CapabilityChanges<P>,
        capabilities: &mut impl PlaceCapabilitiesInterface<'tcx, CapabilityKind, P>,
        ctxt: Ctxt,
    ) -> bool
    where
        'tcx: 'a,
        EdgeKind: LabelEdgeLifetimeProjections<'tcx, Ctxt, P> + Eq + std::hash::Hash,
        VC: ValidityConditionOps<Ctxt>,
    {
        let changed = changes.apply(capabilities, ctxt);
        for (place, cap) in changes.iter() {
            if cap.is_some_and(|cap| !cap.is_read()) {
                capabilities.resume(place);
            }
            if cap == Some(CapabilityKind::Exclusive) {
                self.label_lifetime_projections(
                    &LabelNodePredicate::all_future_postfixes(place),
                    None,
                    ctxt,
                );
            }
        }
        changed
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
        for lifetime in arg_place.generalized_lifetimes(ctxt) {
            let source_projection: LifetimeProjection<'tcx, RemotePlace> =
                LifetimeProjection::new(RemotePlace::new(local), lifetime, None, ctxt)
                    .unwrap_or_else(|| {
                        panic!(
                            "Failed to create region for remote place (for {local:?}).
                                    It does not have lifetime {lifetime:?}",
                        );
                    });
            let source_projection: LifetimeProjection<'tcx, PcgLifetimeProjectionBase<'tcx>> =
                source_projection.rebase();
            let target_projection = LifetimeProjection::<'tcx, MaybeLabelledPlace<'tcx>>::new(
                MaybeLabelledPlace::Current(arg_place),
                lifetime,
                None,
                ctxt,
            )
            .unwrap();
            assert!(
                self.apply_action(
                    &mut BorrowPcgAction::add_edge(
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
