//! The join of PCG states. The joined state holds the meet of the
//! predecessors' capabilities, and each predecessor reaches it through
//! explicit actions.

use std::cmp::Reverse;

use crate::{
    action::{AppliedActions, BorrowPcgAction, OwnedPcgAction, PcgAction},
    borrow_pcg::{
        action::LabelPlaceReason,
        borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike},
        edge::kind::BorrowPcgEdgeKind,
        edge_data::EdgeData,
        graph::BorrowsGraph,
    },
    error::PcgError,
    r#loop::PlaceUsageType,
    owned_pcg::RepackOp,
    pcg::{
        CapabilityKind, PcgMutRef, PcgRefLike,
        obtain::{HasSnapshotLocation, ObtainType, PlaceObtainer, expand::PlaceExpander},
        owned_state::OwnedPcg,
        place_capabilities::{
            PlaceCapabilities, PlaceCapabilitiesInterface, PlaceCapabilitiesReader,
        },
    },
    pcg_validity_assert,
    rustc_interface::middle::mir::{self, ProjectionElem},
    utils::{
        DataflowCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, HasPlace, Place, PlaceLike,
        SnapshotLocation,
        data_structures::HashSet,
        display::{DebugLines, DisplayWithCompilerCtxt},
    },
};

use super::{Pcg, is_variant_unpacking};

/// The capability of a place in the join of two paths that hold it with `a`
/// and `b`: the lower one. A reference that one path holds frozen (R) and
/// the other with its referent lent (e) keeps its own value: e. A place that
/// one path holds frozen and the other has moved out (W) can only be
/// overwritten: W. Neither holds while a loan keeps the place frozen (see
/// `Pcg::joined_capabilities`).
pub(crate) fn meet(a: CapabilityKind, b: CapabilityKind) -> CapabilityKind {
    match (a, b) {
        (CapabilityKind::Read, CapabilityKind::ShallowExclusive)
        | (CapabilityKind::ShallowExclusive, CapabilityKind::Read) => {
            CapabilityKind::ShallowExclusive
        }
        _ => a.minimum(b).unwrap_or(CapabilityKind::Write),
    }
}

/// The capability `place` has in `capabilities` or, if it has none, gets by
/// unpacking its closest ancestor that has one. Unpacking enters an enum
/// variant only if `enter_variants`: a variant is known only on the paths
/// that matched it.
fn unpacked_capability<'a, 'tcx: 'a>(
    capabilities: &PlaceCapabilities<'tcx>,
    place: Place<'tcx>,
    enter_variants: bool,
    ctxt: impl HasCompilerCtxt<'a, 'tcx>,
) -> Option<CapabilityKind> {
    unpacked(|p| capabilities.get(p, ctxt), place, enter_variants, ctxt)
}

/// The capability `place` has in `lookup` or, if it has none, gets by
/// unpacking its closest ancestor that has one; see [`unpacked_capability`].
pub(crate) fn unpacked<'a, 'tcx: 'a>(
    lookup: impl Fn(Place<'tcx>) -> Option<CapabilityKind>,
    place: Place<'tcx>,
    enter_variants: bool,
    ctxt: impl HasCompilerCtxt<'a, 'tcx>,
) -> Option<CapabilityKind> {
    let (ancestor, mut capability) = std::iter::successors(Some(place), |p| p.parent_place())
        .find_map(|p| Some((p, lookup(p)?)))?;
    for (base, elem) in place.iter_projections_after(ancestor, ctxt)? {
        capability = match (elem, capability) {
            (ProjectionElem::Downcast(..), _) if !enter_variants => return None,
            (ProjectionElem::Deref, _) if base.is_raw_ptr(ctxt) => return None,
            (ProjectionElem::Deref, CapabilityKind::Exclusive) if !base.is_shared_ref(ctxt) => {
                CapabilityKind::Exclusive
            }
            (ProjectionElem::Deref, CapabilityKind::Exclusive | CapabilityKind::Read) => {
                CapabilityKind::Read
            }
            (ProjectionElem::Deref, _) => return None,
            _ => capability,
        };
    }
    Some(capability)
}

/// The capability `place` gets when what lies below it is packed into it:
/// the meet of the capabilities below it, none if a leaf of its layout (an
/// owned expansion or a borrow-PCG expansion) has none (it is borrowed).
fn packed_capability<'a, 'tcx: 'a>(
    capabilities: &PlaceCapabilities<'tcx>,
    owned: &OwnedPcg<'tcx>,
    graph: &BorrowsGraph<'tcx>,
    place: Place<'tcx>,
    ctxt: impl HasCompilerCtxt<'a, 'tcx>,
) -> Option<CapabilityKind> {
    if let Some(capability) = unpacked_capability(capabilities, place, false, ctxt) {
        return Some(capability);
    }
    let owned_leaves = owned
        .is_allocated(place.local)
        .then(|| owned[place.local].expansions().leaf_places(ctxt))
        .into_iter()
        .flatten()
        .map(Place::from);
    let borrowed_expansions = graph
        .edges
        .keys()
        .filter_map(|kind| match kind {
            BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) => Some(expansion),
            _ => None,
        })
        .collect::<Vec<_>>();
    let borrowed_leaves = borrowed_expansions
        .iter()
        .flat_map(|expansion| {
            expansion
                .expansion()
                .iter()
                .filter_map(|node| node.as_current_place())
                .collect::<Vec<_>>()
        })
        .filter(|part| {
            !borrowed_expansions
                .iter()
                .any(|expansion| expansion.base().as_current_place() == Some(*part))
        });
    if owned_leaves
        .chain(borrowed_leaves)
        .any(|leaf| place.is_prefix_of(leaf) && capabilities.get(leaf, ctxt).is_none())
    {
        return None;
    }
    capabilities
        .iter()
        .filter(|(p, _)| place.is_strict_prefix_of(*p))
        .map(|(_, capability)| capability)
        .reduce(meet)
}

impl<'a, 'tcx: 'a> Pcg<'a, 'tcx> {
    /// Joins `other` into this state, which reaches the meet of both.
    pub(crate) fn join_with(
        &mut self,
        other: &Self,
        self_block: mir::BasicBlock,
        snapshot: SnapshotLocation,
        ctxt: impl DataflowCtxt<'a, 'tcx>,
    ) -> Result<(), PcgError> {
        let joined = self.joined_capabilities(other, ctxt);
        self.reach(&joined, other, self_block, snapshot, ctxt)?;
        Ok(())
    }

    /// The capabilities of the join of this state and `other`: the meet of
    /// the capabilities each path has or gets by unpacking. Where one path
    /// holds the place frozen (R) and the meet is more than R (e or W), there
    /// is none while a loan of either path blocks the place or a place it is
    /// part of: the loan keeps it frozen. Where the paths unpack different
    /// variants of an enum, the join holds the enum packed.
    fn joined_capabilities(
        &self,
        other: &Self,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> PlaceCapabilities<'tcx> {
        let places = self
            .place_capabilities
            .iter()
            .chain(other.place_capabilities.iter())
            .map(|(place, _)| place)
            .collect::<HashSet<_>>();
        let lent = self
            .borrow
            .graph
            .lent_places(ctxt.bc_ctxt())
            .into_iter()
            .chain(other.borrow.graph.lent_places(ctxt.bc_ctxt()))
            .collect::<Vec<_>>();
        let mut joined = PlaceCapabilities::default();
        for place in places {
            let capability = match (
                unpacked_capability(&self.place_capabilities, place, false, ctxt),
                unpacked_capability(&other.place_capabilities, place, false, ctxt),
            ) {
                (Some(a), Some(b)) => Some(meet(a, b))
                    .filter(|capability| {
                        capability.is_read()
                            || !(a.is_read() || b.is_read())
                            || !lent.iter().any(|lent| lent.is_prefix_of(place))
                    })
                    .map(|capability| (place, capability)),
                (Some(_), None) | (None, Some(_)) => self
                    .diverging_variant_base(other, place, ctxt)
                    .and_then(|base| {
                        Some((
                            base,
                            meet(
                                packed_capability(
                                    &self.place_capabilities,
                                    &self.owned,
                                    &self.borrow.graph,
                                    base,
                                    ctxt,
                                )?,
                                packed_capability(
                                    &other.place_capabilities,
                                    &other.owned,
                                    &other.borrow.graph,
                                    base,
                                    ctxt,
                                )?,
                            ),
                        ))
                    }),
                (None, None) => None,
            };
            if let Some((place, capability)) = capability {
                joined.insert(place, capability, ctxt);
            }
        }
        let packed = joined
            .iter()
            .filter(|(_, capability)| {
                matches!(
                    capability,
                    CapabilityKind::Exclusive | CapabilityKind::Write
                )
            })
            .map(|(place, _)| place)
            .collect::<Vec<_>>();
        joined.retain(|place, _| !packed.iter().any(|p| p.is_strict_prefix_of(place)));
        joined
    }

    /// The enum place above `place` whose variant only one of the paths has
    /// unpacked.
    fn diverging_variant_base(
        &self,
        other: &Self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Option<Place<'tcx>> {
        let knows = |pcg: &Self, variant: Place<'tcx>| {
            pcg.place_capabilities
                .iter()
                .any(|(p, _)| variant.is_prefix_of(p))
        };
        let projections = place
            .iter_projections_after(place.local.into(), ctxt)?
            .collect::<Vec<_>>();
        projections
            .iter()
            .enumerate()
            .find_map(|(i, (base, elem))| {
                let variant = projections.get(i + 1).map_or(place, |(p, _)| *p);
                (matches!(elem, ProjectionElem::Downcast(..))
                    && knows(self, variant) != knows(other, variant))
                .then_some(*base)
            })
    }

    /// Gives this state the capabilities `target`, recording the actions.
    /// `other` is the state across the join: the places this state holds and
    /// `target` does not are lent to the edges of `other` that block them.
    pub(crate) fn reach(
        &mut self,
        target: &PlaceCapabilities<'tcx>,
        other: &Self,
        self_block: mir::BasicBlock,
        snapshot: SnapshotLocation,
        ctxt: impl DataflowCtxt<'a, 'tcx>,
    ) -> Result<Vec<PcgAction<'tcx>>, PcgError> {
        let mut applied = AppliedActions::default();
        PlaceObtainer::new(
            PcgMutRef::from(&mut *self),
            Some(&mut applied),
            ctxt,
            snapshot.location(),
            snapshot,
        )
        .reach(target, other, self_block)?;
        self.owned.join_capabilities(&other.owned);
        pcg_validity_assert!(
            self.place_capabilities.map == target.map,
            [ctxt],
            "the join reaches {:?} instead of {:?}",
            self.place_capabilities.debug_lines(ctxt),
            target.debug_lines(ctxt)
        );
        Ok(applied.actions.into_iter().map(|a| a.action).collect())
    }

    /// Gives this state the owned layout that `other` has below the places
    /// neither holds: the parts that are lent or blocked on the other path.
    /// It changes no capability.
    pub(crate) fn join_lent_layout(&mut self, other: &Self, ctxt: impl DataflowCtxt<'a, 'tcx>) {
        for local in (0..self.owned.num_locals()).map(mir::Local::from) {
            if !self.owned.is_allocated(local) || !other.owned.is_allocated(local) {
                continue;
            }
            let mut expansions = other.owned[local]
                .expansions()
                .expansions()
                .iter()
                .cloned()
                .collect::<Vec<_>>();
            expansions.sort_by_key(|expanded| expanded.place.projection.len());
            for expanded in expansions {
                let layout = self.owned[local].expansions();
                if layout.expansions().contains(&expanded)
                    || !layout.contains_place(expanded.place, ctxt.bc_ctxt())
                {
                    continue;
                }
                pcg_validity_assert!(
                    self.place_capabilities.get(expanded.place, ctxt).is_none(),
                    [ctxt],
                    "the join unpacks {}, which holds a capability",
                    expanded.place.display_string(ctxt.bc_ctxt())
                );
                self.owned[local]
                    .expansions_mut()
                    .insert_expansion(expanded.place, expanded.expansion);
            }
        }
    }

    /// The capabilities that the join of `states` suspends: at the finest
    /// places that every state records or covers (a recorded place or one
    /// above it, such as the enum whose variants the states unpack
    /// differently), the meet of what each state has for them. A reference
    /// and its referent are separate places.
    pub(crate) fn joined_suspended(
        states: &[&Self],
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> PlaceCapabilities<'tcx> {
        let covered = states
            .iter()
            .flat_map(|state| state.place_capabilities.iter_suspended())
            .flat_map(|(place, _)| std::iter::successors(Some(place), |p| p.parent_place()))
            .collect::<HashSet<_>>()
            .into_iter()
            .filter_map(|place| {
                let capability = states
                    .iter()
                    .map(|state| state.covered_suspended(place, ctxt))
                    .collect::<Option<Vec<_>>>()?
                    .into_iter()
                    .reduce(meet)?;
                Some((place, capability))
            })
            .collect::<Vec<_>>();
        let mut joined = PlaceCapabilities::default();
        for &(place, capability) in &covered {
            if !covered.iter().any(|(part, _)| {
                place.is_strict_prefix_of(*part) && !part.projects_indirection_from(place, ctxt)
            }) {
                joined.suspend(place, capability);
            }
        }
        joined
    }

    /// The capability suspended for `place`, or for it as part of a lent
    /// ancestor, or for its lent parts together when nothing of its value is
    /// held.
    fn covered_suspended(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Option<CapabilityKind> {
        let in_value =
            |p: Place<'tcx>| place.is_prefix_of(p) && !p.projects_indirection_from(place, ctxt);
        unpacked(|p| self.place_capabilities.suspended(p), place, false, ctxt).or_else(|| {
            if self.place_capabilities.iter().any(|(p, _)| in_value(p)) {
                return None;
            }
            self.place_capabilities
                .iter_suspended()
                .filter(|(p, _)| in_value(*p))
                .map(|(_, capability)| capability)
                .reduce(meet)
        })
    }

    /// Gives this state the suspended capabilities `target`, recording the
    /// actions.
    pub(crate) fn reach_suspended(
        &mut self,
        target: &PlaceCapabilities<'tcx>,
        snapshot: SnapshotLocation,
        ctxt: impl DataflowCtxt<'a, 'tcx>,
    ) -> Result<Vec<PcgAction<'tcx>>, PcgError> {
        let mut applied = AppliedActions::default();
        PlaceObtainer::new(
            PcgMutRef::from(self),
            Some(&mut applied),
            ctxt,
            snapshot.location(),
            snapshot,
        )
        .reach_suspended(target)?;
        Ok(applied.actions.into_iter().map(|a| a.action).collect())
    }
}

/// Where the places a path gives up at a join are lent: to the edges of the
/// state across the join that the path did not have before the join.
struct Lending<'r, 'a, 'tcx> {
    other: &'r Pcg<'a, 'tcx>,
    own_edges: &'r HashSet<BorrowPcgEdgeKind<'tcx>>,
    self_block: mir::BasicBlock,
}

impl<'a, 'tcx: 'a> Lending<'_, 'a, 'tcx> {
    /// The edge that `blocked` is lent to: one that is a loan, not an
    /// unpacking (except of an enum variant this path did not match).
    fn edge(
        &self,
        blocked: Place<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Option<BorrowPcgEdge<'tcx>> {
        self.other
            .borrow
            .graph()
            .edges_blocking(blocked.into(), ctxt.bc_ctxt())
            .filter(|edge| {
                (is_variant_unpacking(edge.kind()) || edge.kind().is_loan())
                    && !self.own_edges.contains(edge.kind())
            })
            .min_by_key(|edge| format!("{:?}", edge.kind()))
            .map(|edge| {
                let mut edge = edge.to_owned_edge();
                edge.conditions = edge.conditions.without_branch_choice(self.self_block);
                edge
            })
    }
}

impl<'pcg, 'a: 'pcg, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PlaceObtainer<'pcg, 'a, 'tcx, Ctxt> {
    fn reach(
        &mut self,
        target: &PlaceCapabilities<'tcx>,
        other: &Pcg<'a, 'tcx>,
        self_block: mir::BasicBlock,
    ) -> Result<(), PcgError> {
        for local in (0..self.pcg.owned.num_locals()).map(mir::Local::from) {
            if self.pcg.owned.is_allocated(local) && !other.owned.is_allocated(local) {
                self.storage_dead(local)?;
            }
        }
        let own_edges = self
            .pcg
            .borrow
            .graph
            .edges
            .keys()
            .cloned()
            .collect::<HashSet<_>>();
        let lending = Lending {
            other,
            own_edges: &own_edges,
            self_block,
        };
        self.move_capabilities_to(target, &lending)?;
        self.unpack_to(target, other)?;
        self.move_capabilities_to(target, &lending)?;
        self.pack_to(target)?;
        self.give_up_places_outside(target, &lending)
    }

    /// Gives this state the suspended capabilities `target`: each place of
    /// `target` gets its record by unpacking the record of a lent ancestor
    /// or packing those of its lent parts, then weakened to the target; the
    /// other records are dropped.
    pub(crate) fn reach_suspended(
        &mut self,
        target: &PlaceCapabilities<'tcx>,
    ) -> Result<(), PcgError> {
        let mut places = target.iter_suspended().collect::<Vec<_>>();
        places.sort_by_key(|(place, _)| (place.projection.len(), *place));
        for &(place, _) in &places {
            if self.pcg.place_capabilities.suspended(place).is_none() {
                match std::iter::successors(place.parent_place(), |p| p.parent_place())
                    .find(|p| self.pcg.place_capabilities.suspended(*p).is_some())
                {
                    Some(ancestor) => self.unpack_suspended_to(ancestor, place)?,
                    None => self.record_and_apply_action(
                        BorrowPcgAction::pack_suspended(place, "join").into(),
                    )?,
                }
            }
        }
        for (place, to) in places {
            if let Some(from) = self.pcg.place_capabilities.suspended(place)
                && meet(from, to) != from
            {
                self.record_and_apply_action(
                    BorrowPcgAction::weaken_suspended(place, from, Some(meet(from, to)), "join")
                        .into(),
                )?;
            }
        }
        let mut dropped = self
            .pcg
            .place_capabilities
            .iter_suspended()
            .filter(|(place, _)| target.suspended(*place).is_none())
            .collect::<Vec<_>>();
        dropped.sort_by_key(|(place, _)| *place);
        for (place, from) in dropped {
            self.record_and_apply_action(
                BorrowPcgAction::weaken_suspended(place, from, None, "join").into(),
            )?;
        }
        Ok(())
    }

    /// Unpacks the capability suspended for `ancestor` level by level down to
    /// `place`.
    fn unpack_suspended_to(
        &mut self,
        ancestor: Place<'tcx>,
        place: Place<'tcx>,
    ) -> Result<(), PcgError> {
        for (base, _) in place
            .iter_projections_after(ancestor, self.ctxt)
            .into_iter()
            .flatten()
        {
            let parts = base.expand_one_level(place, self.ctxt)?.expansion();
            self.record_and_apply_action(
                BorrowPcgAction::unpack_suspended(base, parts, "join").into(),
            )?;
        }
        Ok(())
    }

    fn storage_dead(&mut self, local: mir::Local) -> Result<(), PcgError> {
        self.record_and_apply_action(
            BorrowPcgAction::label_place_and_update_related_capabilities(
                local.into(),
                self.prev_snapshot_location(),
                LabelPlaceReason::StorageDead,
            )
            .into(),
        )?;
        self.obtain(local.into(), ObtainType::ForStorageDead)?;
        self.record_and_apply_action(
            OwnedPcgAction::new(RepackOp::StorageDead(local), Some("join".into())).into(),
        )
    }

    /// Unpacks this state down to the places `target` holds; into a loop
    /// head, as the loop invariant unpacks them.
    fn unpack_to(
        &mut self,
        target: &PlaceCapabilities<'tcx>,
        other: &Pcg<'a, 'tcx>,
    ) -> Result<(), PcgError> {
        let mut places = target.iter().map(|(place, _)| place).collect::<Vec<_>>();
        places.sort_by_key(|place| place.projection.len());
        for place in places {
            if self.pcg.place_capabilities.get(place, self.ctxt).is_none()
                && let Some(capability) =
                    unpacked_capability(self.pcg.place_capabilities, place, true, self.ctxt)
            {
                let obtain_type = match self.prev_snapshot_location() {
                    SnapshotLocation::Loop(_) => ObtainType::LoopInvariant {
                        is_blocked: false,
                        usage_type: if capability.is_read() {
                            PlaceUsageType::Read
                        } else {
                            PlaceUsageType::Exclusive
                        },
                    },
                    _ => ObtainType::Capability(capability),
                };
                self.expand_to(place, Some(other.borrow.graph()), obtain_type, self.ctxt)?;
            }
        }
        Ok(())
    }

    /// Moves the capability of each place this state holds to the one it
    /// has or gets by unpacking in `target`; a frozen place that `target`
    /// unpacks exclusively is unfrozen to be unpacked, one whose parts
    /// `target` only reads has its freeze moved to its read copies, and a
    /// place this state unpacks exclusively that `target` reads is frozen.
    /// Read copies follow the place they are copied from.
    fn move_capabilities_to(
        &mut self,
        target: &PlaceCapabilities<'tcx>,
        lending: &Lending<'_, 'a, 'tcx>,
    ) -> Result<(), PcgError> {
        let mut places = self
            .pcg
            .place_capabilities
            .iter()
            .chain(target.iter().filter(|(_, capability)| capability.is_read()))
            .map(|(place, _)| place)
            .collect::<HashSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        places.sort_by_key(|place| place.projection.len());
        for place in places {
            let Some(from) = self.pcg.place_capabilities.get(place, self.ctxt) else {
                if target.get(place, self.ctxt) == Some(CapabilityKind::Read)
                    && self.pcg.place_capabilities.unpacks(place)
                {
                    self.record_and_apply_action(BorrowPcgAction::freeze(place, "join").into())?;
                }
                continue;
            };
            let is_read_copy = from == CapabilityKind::Read
                && place.parent_place().is_some_and(|parent| {
                    self.pcg
                        .place_capability_equals(parent, CapabilityKind::Read, self.ctxt)
                });
            let unpacked =
                target.get(place, self.ctxt) != Some(CapabilityKind::Read) && target.unpacks(place);
            if unpacked
                && from == CapabilityKind::Read
                && !is_read_copy
                && target
                    .capabilities_for_strict_postfixes_of(place)
                    .all(|(_, capability)| capability.is_read())
            {
                self.refreeze_to_copies(place)?;
                continue;
            }
            let to = if unpacked {
                (from == CapabilityKind::Read).then_some(CapabilityKind::Exclusive)
            } else {
                unpacked_capability(target, place, true, self.ctxt)
            };
            if let Some(to) = to
                && to != from
                && !is_read_copy
            {
                self.move_capability(place, from, to, target, lending)?;
            }
        }
        Ok(())
    }

    /// Moves the freeze of `place` to its read copies one level down, if it
    /// has been unpacked.
    fn refreeze_to_copies(&mut self, place: Place<'tcx>) -> Result<(), PcgError> {
        let mut copies = self
            .pcg
            .place_capabilities
            .capabilities_for_strict_postfixes_of(place)
            .filter(|(copy, _)| copy.parent_place() == Some(place))
            .map(|(copy, _)| copy)
            .collect::<Vec<_>>();
        copies.sort();
        if copies.is_empty() {
            return Ok(());
        }
        self.record_and_apply_action(BorrowPcgAction::refreeze(place, copies, "join").into())
    }

    fn move_capability(
        &mut self,
        place: Place<'tcx>,
        from: CapabilityKind,
        to: CapabilityKind,
        target: &PlaceCapabilities<'tcx>,
        lending: &Lending<'_, 'a, 'tcx>,
    ) -> Result<(), PcgError> {
        match (from, to) {
            (CapabilityKind::ShallowExclusive, CapabilityKind::Exclusive) => {
                self.remove_edges_absent_from(place, lending.other)
            }
            (
                CapabilityKind::Exclusive | CapabilityKind::ShallowExclusive,
                CapabilityKind::Read,
            ) => self.record_and_apply_action(BorrowPcgAction::freeze(place, "join").into()),
            (CapabilityKind::Read | CapabilityKind::ShallowExclusive, CapabilityKind::Write) => {
                self.obtain(place, ObtainType::Capability(CapabilityKind::Write))?;
                self.weaken_to(place, to)
            }
            (CapabilityKind::Read, _) => {
                self.upgrade_read_to_exclusive(place, &|base| target.unpacks(base))?;
                self.weaken_to(place, to)
            }
            // The referent of a mutable reference is lent, through the
            // reference, to the edge of `other` that blocks it.
            (CapabilityKind::Exclusive, CapabilityKind::ShallowExclusive)
                if place.is_mut_ref(self.ctxt)
                    && let Some(edge) = lending.edge(place.project_deref(self.ctxt), self.ctxt) =>
            {
                self.record_and_apply_action(
                    BorrowPcgAction::lend(place.project_deref(self.ctxt), edge, "join").into(),
                )
            }
            (
                CapabilityKind::Exclusive,
                CapabilityKind::ShallowExclusive | CapabilityKind::Write,
            ) => self.weaken_to(place, to),
            _ => {
                let ctxt = self.ctxt;
                pcg_validity_assert!(
                    false,
                    [ctxt],
                    "{} cannot go from {from:?} to {to:?} at a join",
                    place.display_string(self.ctxt.bc_ctxt())
                );
                Ok(())
            }
        }
    }

    /// Removes the edges that `other` does not have and that block `place`,
    /// its postfixes or, transitively, what they are lent to, leaves first,
    /// regaining the capabilities they block. Into a loop head, its loop
    /// abstraction stands for them.
    fn remove_edges_absent_from(
        &mut self,
        place: Place<'tcx>,
        other: &Pcg<'a, 'tcx>,
    ) -> Result<(), PcgError> {
        let ctxt = self.ctxt;
        let mut lent = vec![place];
        let mut absent = vec![];
        let mut changed = true;
        while changed {
            changed = false;
            for edge in self.pcg.borrow.graph.edges() {
                let kind = edge.kind();
                if absent.contains(kind)
                    || other.borrow.graph().edges.contains_key(kind)
                    || !kind.blocked_nodes(ctxt.bc_ctxt()).any(|node| {
                        node.related_maybe_labelled_place()
                            .is_some_and(|p| lent.iter().any(|l| l.is_prefix_of(p.place())))
                    })
                {
                    continue;
                }
                lent.extend(
                    kind.blocked_by_nodes(ctxt.bc_ctxt())
                        .map(|node| node.place()),
                );
                absent.push(kind.clone());
                changed = true;
            }
        }
        loop {
            let fg = self.pcg.borrow.graph.frozen_graph();
            let Some(edge) = fg
                .leaf_edges(ctxt)
                .into_iter()
                .map(BorrowPcgEdgeLike::to_owned_edge)
                .find(|edge| absent.contains(edge.kind()))
            else {
                return Ok(());
            };
            self.remove_edge_and_perform_associated_state_updates(&edge, "join")?;
        }
    }

    /// Weakens `place` to `to` if it holds more.
    fn weaken_to(&mut self, place: Place<'tcx>, to: CapabilityKind) -> Result<(), PcgError> {
        match self.pcg.capability_of(place, self.ctxt) {
            Some(from) if from > to => self
                .record_and_apply_action(BorrowPcgAction::weaken(place, from, to, "join").into()),
            _ => Ok(()),
        }
    }

    /// Weakens to [`CapabilityKind::Write`] the owned places that are not
    /// definitely initialized here, held or suspended, and the local
    /// references that are dead here.
    pub(super) fn weaken_maybe_uninitialized(&mut self) -> Result<(), PcgError> {
        let ctxt = self.ctxt;
        let location = self.location();
        let body_analysis = ctxt.body_analysis();
        let suspended = self
            .pcg
            .place_capabilities
            .iter_suspended()
            .filter(|(place, capability)| {
                *capability > CapabilityKind::Write
                    && place.as_owned_place(ctxt).is_some()
                    && !body_analysis.is_definitely_initialized_at(location, *place)
            })
            .collect::<Vec<_>>();
        for (place, from) in suspended {
            self.record_and_apply_action(
                BorrowPcgAction::weaken_suspended(
                    place,
                    from,
                    Some(CapabilityKind::Write),
                    "loop head",
                )
                .into(),
            )?;
        }
        let mut places = self
            .pcg
            .place_capabilities
            .iter()
            .filter_map(|(place, capability)| {
                (capability != CapabilityKind::Write
                    && (!body_analysis.is_definitely_initialized_at(location, place)
                        || matches!(
                            capability,
                            CapabilityKind::Exclusive | CapabilityKind::ShallowExclusive
                        ) && place.projection.is_empty()
                            && !place.lifetime_projections(ctxt).is_empty()
                            && !body_analysis.is_live_and_initialized_at(location, place)))
                .then(|| place.as_owned_place(ctxt))
                .flatten()
            })
            .collect::<Vec<_>>();
        places.sort_by_key(|owned| owned.place().projection.len());
        for owned in places {
            let place = owned.place();
            if self.pcg.place_capabilities.get(place, ctxt).is_some() {
                self.obtain(place, ObtainType::Capability(CapabilityKind::Write))?;
                self.weaken_to(place, CapabilityKind::Write)?;
                self.pcg
                    .owned
                    .apply_capability_change(owned, CapabilityKind::Write, ctxt);
            }
        }
        Ok(())
    }

    /// Packs what this state holds below the places `target` holds packed.
    fn pack_to(&mut self, target: &PlaceCapabilities<'tcx>) -> Result<(), PcgError> {
        let mut places = target.iter().collect::<Vec<_>>();
        places.sort_by_key(|(place, _)| Reverse(place.projection.len()));
        for (place, capability) in places {
            if !self
                .pcg
                .place_capabilities
                .capabilities_for_strict_postfixes_of(place)
                .any(|(p, _)| target.get(p, self.ctxt).is_none())
            {
                continue;
            }
            self.pack(place, capability, &|base| target.unpacks(base))?;
        }
        Ok(())
    }

    /// Packs what this state holds below `place` into `place` at
    /// `capability`, keeping the read unpackings of the places `keep` holds.
    fn pack(
        &mut self,
        place: Place<'tcx>,
        capability: CapabilityKind,
        keep: &impl Fn(Place<'tcx>) -> bool,
    ) -> Result<(), PcgError> {
        match capability {
            CapabilityKind::Read => {
                self.detach_borrowed_shared_referents(place, keep)?;
                self.pack_read_unpacking(place, keep)
            }
            CapabilityKind::Exclusive | CapabilityKind::Write => {
                self.obtain(place, ObtainType::Capability(capability))
            }
            CapabilityKind::ShallowExclusive => Ok(()),
        }
    }

    /// Gives up the places this state holds and `target` does not: each is
    /// lent to the edge of `other` that blocks it, or to the loan of this
    /// state that still blocks it, or, where `other` unpacked it further and
    /// lent its parts, unpacked to lend those. Otherwise the value of the
    /// place on this path is detached from it.
    fn give_up_places_outside(
        &mut self,
        target: &PlaceCapabilities<'tcx>,
        lending: &Lending<'_, 'a, 'tcx>,
    ) -> Result<(), PcgError> {
        let ctxt = self.ctxt;
        let other = lending.other;
        while let Some((place, capability)) = self
            .pcg
            .place_capabilities
            .iter()
            .filter(|(place, _)| target.get(*place, ctxt).is_none())
            .min_by_key(|(place, _)| (place.projection.len(), *place))
        {
            let lending_edge = |blocked| lending.edge(blocked, ctxt);
            let lent_part = || {
                other
                    .borrow
                    .graph()
                    .edges()
                    .flat_map(|edge| {
                        edge.kind()
                            .blocked_nodes(ctxt.bc_ctxt())
                            .collect::<Vec<_>>()
                    })
                    .filter_map(|node| node.related_maybe_labelled_place()?.as_current_place())
                    .filter(|blocked| place.is_strict_prefix_of(*blocked))
                    .find_map(|blocked| Some((blocked, lending_edge(blocked)?)))
            };
            let place_lent_to = std::iter::successors(Some(place), |p| p.parent_place())
                .find_map(|lent| Some((lent, lending_edge(lent)?)));
            // Each part this path holds of a lent place is lent with what it
            // holds.
            if let Some((_, edge)) = place_lent_to {
                self.record_and_apply_action(BorrowPcgAction::lend(place, edge, "join").into())?;
                continue;
            }
            // A place that a loan of this path still blocks, directly or as
            // part of a lent place, stays with that loan; a place in a value
            // that the join gives up as a whole goes with the loan of this
            // path on another part of that value.
            let given_up = std::iter::successors(Some(place), |p| p.parent_place())
                .take_while(|value| {
                    !place.projects_indirection_from(*value, ctxt)
                        && !target.iter().any(|(held, _)| value.is_prefix_of(held))
                })
                .last()
                .unwrap_or(place);
            let own_loan = self
                .pcg
                .borrow
                .graph
                .edges()
                .filter(|edge| edge.kind().is_loan())
                .filter_map(|edge| {
                    let holds_place = edge
                        .kind()
                        .blocked_nodes(ctxt.bc_ctxt())
                        .filter_map(|node| node.as_current_place())
                        .filter(|blocked| {
                            given_up.is_prefix_of(*blocked) || blocked.is_prefix_of(place)
                        })
                        .map(|blocked| blocked.is_prefix_of(place))
                        .max()?;
                    Some((!holds_place, edge.to_owned_edge()))
                })
                .min_by_key(|(elsewhere, edge)| (*elsewhere, format!("{:?}", edge.kind())))
                .map(|(_, edge)| edge);
            if let Some(edge) = own_loan {
                self.record_and_apply_action(BorrowPcgAction::lend(place, edge, "join").into())?;
                continue;
            }
            if let Some((part, edge)) = lent_part() {
                // This path holds `place` packed, so it did not match an enum
                // variant on the way to the part: the place itself is lent.
                if part
                    .iter_projections_after(place, ctxt)
                    .is_some_and(|mut projections| {
                        projections.any(|(_, elem)| matches!(elem, ProjectionElem::Downcast(..)))
                    })
                {
                    self.record_and_apply_action(
                        BorrowPcgAction::lend(place, edge, "join").into(),
                    )?;
                    continue;
                }
                self.expand_to(
                    part,
                    Some(other.borrow.graph()),
                    ObtainType::Capability(capability),
                    ctxt,
                )?;
                // A frozen place's freeze moves to its read copies, which
                // are lent or given up apart.
                if capability == CapabilityKind::Read {
                    self.refreeze_to_copies(place)?;
                    continue;
                }
            }
            if self.pcg.place_capabilities.get(place, ctxt).is_some() {
                self.record_and_apply_action(
                    BorrowPcgAction::label_place_and_update_related_capabilities(
                        place,
                        self.prev_snapshot_location(),
                        LabelPlaceReason::Detach,
                    )
                    .into(),
                )?;
            }
        }
        Ok(())
    }
}
