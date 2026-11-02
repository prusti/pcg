//! The join of PCG states. The joined state holds the meet of the
//! predecessors' capabilities, and each predecessor reaches it through
//! explicit actions.

use std::cmp::Reverse;

use crate::{
    action::{AppliedActions, BorrowPcgAction, OwnedPcgAction, PcgAction},
    borrow_pcg::{
        action::LabelPlaceReason, borrow_pcg_edge::BorrowPcgEdgeLike,
        edge::kind::BorrowPcgEdgeKind, edge_data::EdgeData,
    },
    error::PcgError,
    r#loop::PlaceUsageType,
    owned_pcg::RepackOp,
    pcg::{
        CapabilityKind, PcgMutRef, PcgRefLike,
        obtain::{HasSnapshotLocation, ObtainType, PlaceObtainer, expand::PlaceExpander},
        place_capabilities::{
            PlaceCapabilities, PlaceCapabilitiesInterface, PlaceCapabilitiesReader,
        },
    },
    pcg_validity_assert,
    rustc_interface::middle::mir::{self, ProjectionElem},
    utils::{
        DataflowCtxt, HasCompilerCtxt, HasPlace, Place, SnapshotLocation,
        data_structures::HashSet,
        display::{DebugLines, DisplayWithCompilerCtxt},
    },
};

use super::{Pcg, is_variant_unpacking};

/// The capability of a place in the join of two paths that hold it with `a`
/// and `b`: the lower one. A reference that one path holds frozen (R) and
/// the other with its referent lent (e) keeps its own value: e. A place that
/// one path holds frozen and the other has moved out (W) can only be
/// overwritten: W.
fn meet(a: CapabilityKind, b: CapabilityKind) -> CapabilityKind {
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
    let (ancestor, mut capability) = std::iter::successors(Some(place), |p| p.parent_place())
        .find_map(|p| Some((p, capabilities.get(p, ctxt)?)))?;
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
    /// the capabilities each path has or gets by unpacking. Where the paths
    /// unpack different variants of an enum, the join holds the enum packed.
    fn joined_capabilities(
        &self,
        other: &Self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> PlaceCapabilities<'tcx> {
        let places = self
            .place_capabilities
            .iter()
            .chain(other.place_capabilities.iter())
            .map(|(place, _)| place)
            .collect::<HashSet<_>>();
        let mut joined = PlaceCapabilities::default();
        for place in places {
            let capability = match (
                unpacked_capability(&self.place_capabilities, place, false, ctxt),
                unpacked_capability(&other.place_capabilities, place, false, ctxt),
            ) {
                (Some(a), Some(b)) => Some((place, meet(a, b))),
                (Some(_), None) | (None, Some(_)) => self
                    .diverging_variant_base(other, place, ctxt)
                    .and_then(|base| {
                        Some((
                            base,
                            meet(
                                self.packed_capability(base, ctxt)?,
                                other.packed_capability(base, ctxt)?,
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

    /// The capability `place` gets when what lies below it is packed into
    /// it: the meet of the capabilities below it, none if an owned place
    /// below it has none (it is borrowed).
    fn packed_capability(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Option<CapabilityKind> {
        if let Some(capability) = unpacked_capability(&self.place_capabilities, place, false, ctxt)
        {
            return Some(capability);
        }
        if self.owned.is_allocated(place.local)
            && self.owned[place.local]
                .expansions()
                .leaf_places(ctxt)
                .into_iter()
                .map(Place::from)
                .any(|leaf| {
                    place.is_prefix_of(leaf) && self.place_capabilities.get(leaf, ctxt).is_none()
                })
        {
            return None;
        }
        self.place_capabilities
            .iter()
            .filter(|(p, _)| place.is_strict_prefix_of(*p))
            .map(|(_, capability)| capability)
            .reduce(meet)
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
            self.place_capabilities == *target,
            [ctxt],
            "the join reaches {:?} instead of {:?}",
            self.place_capabilities.debug_lines(ctxt),
            target.debug_lines(ctxt)
        );
        Ok(applied.actions.into_iter().map(|a| a.action).collect())
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
        self.move_capabilities_to(target, other)?;
        self.unpack_to(target, other)?;
        self.move_capabilities_to(target, other)?;
        self.pack_to(target)?;
        self.give_up_places_outside(target, other, self_block)
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
    /// unpacks exclusively is unfrozen to be unpacked, and a place this state
    /// unpacks exclusively that `target` reads is frozen. Read copies follow
    /// the place they are copied from.
    fn move_capabilities_to(
        &mut self,
        target: &PlaceCapabilities<'tcx>,
        other: &Pcg<'a, 'tcx>,
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
            let unpacked_exclusively =
                target.get(place, self.ctxt) != Some(CapabilityKind::Read) && target.unpacks(place);
            let to = if unpacked_exclusively {
                (from == CapabilityKind::Read).then_some(CapabilityKind::Exclusive)
            } else {
                unpacked_capability(target, place, true, self.ctxt)
            };
            if let Some(to) = to
                && to != from
                && !is_read_copy
            {
                self.move_capability(place, from, to, target, other)?;
            }
        }
        Ok(())
    }

    fn move_capability(
        &mut self,
        place: Place<'tcx>,
        from: CapabilityKind,
        to: CapabilityKind,
        target: &PlaceCapabilities<'tcx>,
        other: &Pcg<'a, 'tcx>,
    ) -> Result<(), PcgError> {
        match (from, to) {
            (CapabilityKind::ShallowExclusive, CapabilityKind::Exclusive) => {
                self.remove_edges_absent_from(place, other)
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
    /// definitely initialized here, and the local references that are dead
    /// here.
    pub(super) fn weaken_maybe_uninitialized(&mut self) -> Result<(), PcgError> {
        let ctxt = self.ctxt;
        let location = self.location();
        let body_analysis = ctxt.body_analysis();
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
    /// lent to the edge of `other` that blocks it or, where `other` unpacked
    /// it further and lent its parts, unpacked to lend those. Otherwise the
    /// value of the place on this path is detached from it.
    fn give_up_places_outside(
        &mut self,
        target: &PlaceCapabilities<'tcx>,
        other: &Pcg<'a, 'tcx>,
        self_block: mir::BasicBlock,
    ) -> Result<(), PcgError> {
        let ctxt = self.ctxt;
        while let Some((place, capability)) = self
            .pcg
            .place_capabilities
            .iter()
            .filter(|(place, _)| target.get(*place, ctxt).is_none())
            .min_by_key(|(place, _)| place.projection.len())
        {
            let graph = &self.pcg.borrow.graph;
            let lending_edge = |blocked: Place<'tcx>| {
                other
                    .borrow
                    .graph()
                    .edges_blocking(blocked.into(), ctxt.bc_ctxt())
                    .find(|edge| {
                        (is_variant_unpacking(edge.kind())
                            || !matches!(
                                edge.kind(),
                                BorrowPcgEdgeKind::Deref(_)
                                    | BorrowPcgEdgeKind::RawPtrDeref(_)
                                    | BorrowPcgEdgeKind::BorrowPcgExpansion(_)
                            ))
                            && !graph.edges.contains_key(edge.kind())
                    })
                    .map(|edge| {
                        let mut edge = edge.to_owned_edge();
                        edge.conditions = edge.conditions.without_branch_choice(self_block);
                        edge
                    })
            };
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
            let part_lent = (capability != CapabilityKind::Read)
                .then(lent_part)
                .flatten();
            if let Some((ancestor, edge)) = place_lent_to {
                // A lent ancestor that the join gives up takes the parts this
                // path holds with it, where they can be packed into it.
                let gives_up_ancestor = target.get(ancestor, ctxt).is_none();
                if gives_up_ancestor
                    && ancestor != place
                    && let Some(packed) = self
                        .pcg
                        .place_capabilities
                        .capabilities_for_strict_postfixes_of(ancestor)
                        .map(|(_, capability)| capability)
                        .reduce(meet)
                {
                    self.pack(ancestor, packed, &|_| false)?;
                }
                let lent = if gives_up_ancestor
                    && self.pcg.place_capabilities.get(ancestor, ctxt).is_some()
                {
                    ancestor
                } else {
                    place
                };
                self.record_and_apply_action(BorrowPcgAction::lend(lent, edge, "join").into())?;
                continue;
            }
            if let Some((part, edge)) = part_lent {
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
