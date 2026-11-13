use itertools::Itertools;

use crate::{
    action::BorrowPcgAction,
    borrow_pcg::{
        GeneralizedLifetime,
        borrow_pcg_edge::BorrowPcgEdge,
        edge::{
            borrow_flow::{BorrowFlowEdge, BorrowFlowEdgeKind, private::FutureEdgeKind},
            kind::BorrowPcgEdgeKind,
        },
        edge_data::{EdgeData, LabelNodePredicate},
        region_projection::{LifetimeProjection, LifetimeProjectionIdx, PcgRegion, Region},
        state::BorrowsStateLike,
    },
    error::PcgError,
    pcg::{
        CapabilityKind, PcgNode, PcgRefLike,
        obtain::{HasSnapshotLocation, ObtainType, PlaceObtainer, expand::PlaceExpander},
        place_capabilities::PlaceCapabilitiesReader,
    },
    rustc_interface::index::IndexVec,
    utils::{
        DataflowCtxt, DebugCtxt, Place, PlaceLike, data_structures::HashSet,
        display::DisplayWithCompilerCtxt,
    },
};

impl<'state, 'a: 'state, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx> + DebugCtxt>
    PlaceObtainer<'state, 'a, 'tcx, Ctxt>
{
    /// The frozen place of whose read unpacking `place` is part: the topmost
    /// of `place` and its ancestors that hold R without interruption.
    pub(crate) fn frozen_ancestor(&self, place: Place<'tcx>) -> Place<'tcx> {
        let mut frozen = place;
        while let Some(parent) = frozen.parent_place()
            && self
                .pcg
                .place_capability_equals(parent, CapabilityKind::Read, self.ctxt)
        {
            frozen = parent;
        }
        frozen
    }

    /// The places below `frozen` borrowed by edges other than unpackings.
    /// Borrows behind a shared reference do not hold a freeze.
    fn borrowed_in(&self, frozen: Place<'tcx>) -> Vec<Place<'tcx>> {
        let ctxt = self.ctxt;
        self.pcg
            .borrow
            .graph
            .edges
            .keys()
            .filter(|kind| {
                !matches!(
                    kind,
                    BorrowPcgEdgeKind::BorrowPcgExpansion(_) | BorrowPcgEdgeKind::Deref(_)
                )
            })
            .flat_map(|kind| {
                kind.blocked_nodes(ctxt.bc_ctxt())
                    .filter_map(|node| node.as_current_place())
                    .collect::<Vec<_>>()
            })
            .filter(|place| frozen.is_strict_prefix_of(*place) && !place.projects_shared_ref(ctxt))
            .collect()
    }

    /// Ends the freeze of `frozen`: if parts of its value are still borrowed,
    /// the freeze moves to them and the rest, with `toward` (the place being
    /// obtained), gets E back. The freeze moves to the topmost read copies
    /// that are borrowed or have a borrowed place in their value that their
    /// own read unpacking does not reach.
    pub(crate) fn end_freeze(
        &mut self,
        frozen: Place<'tcx>,
        toward: Option<Place<'tcx>>,
        reason: AdjustCapabilityReason,
    ) -> Result<(), PcgError> {
        let in_value = self.borrowed_in(frozen);
        if !in_value.is_empty() {
            self.unpack_read_toward(frozen, toward, &in_value)?;
        }
        let copies = self
            .pcg
            .place_capabilities
            .capabilities_for_strict_postfixes_of(frozen)
            .map(|(p, _)| p)
            .collect::<Vec<_>>();
        let borrowed = copies
            .iter()
            .copied()
            .filter(|copy| {
                in_value.iter().any(|place| {
                    copy.is_prefix_of(*place)
                        && !copies
                            .iter()
                            .any(|c| copy.is_strict_prefix_of(*c) && c.is_prefix_of(*place))
                })
            })
            .collect::<Vec<_>>();
        let to = borrowed
            .iter()
            .copied()
            .filter(|p| !borrowed.iter().any(|q| q.is_strict_prefix_of(*p)))
            .sorted()
            .collect::<Vec<_>>();
        let action = if to.is_empty() {
            BorrowPcgAction::unfreeze(frozen, format!("{reason:?}"))
        } else {
            BorrowPcgAction::refreeze(frozen, to, format!("{reason:?}"))
        };
        self.record_and_apply_action(action.into())
    }

    /// Unpacks the read unpacking of `frozen` toward `toward`, a part of its
    /// value being obtained, and at each place on the way, one level into
    /// every other unpacking of the layout that holds a place of `borrowed`.
    /// A join that holds an enum packed keeps the layout of a borrowed
    /// variant field but drops its read copies: the freeze moves to the
    /// variant without entering it, and the variant being obtained gets E.
    /// Obtaining `frozen` itself leaves no part to give E back to.
    fn unpack_read_toward(
        &mut self,
        frozen: Place<'tcx>,
        toward: Option<Place<'tcx>>,
        borrowed: &[Place<'tcx>],
    ) -> Result<(), PcgError> {
        let ctxt = self.ctxt;
        let Some(toward) = toward.filter(|place| {
            frozen.is_strict_prefix_of(*place) && !place.projects_indirection_from(frozen, ctxt)
        }) else {
            return Ok(());
        };
        self.expand_to(
            toward,
            None,
            ObtainType::Capability(CapabilityKind::Read),
            ctxt,
        )?;
        let path = std::iter::successors(toward.parent_place(), |p| p.parent_place())
            .take_while(|p| frozen.is_prefix_of(*p))
            .collect::<Vec<_>>();
        let mut beside = self.pcg.owned[frozen.local]
            .expansions()
            .expansions()
            .iter()
            .filter(|expanded| path.contains(&expanded.place))
            .flat_map(|expanded| expanded.expansion_places(ctxt).unwrap())
            .filter(|part| {
                !part.is_prefix_of(toward) && borrowed.iter().any(|b| part.is_prefix_of(*b))
            })
            .collect::<Vec<_>>();
        beside.sort_by_key(|part| (part.projection.len(), *part));
        for part in beside {
            self.expand_to(
                part,
                None,
                ObtainType::Capability(CapabilityKind::Read),
                ctxt,
            )?;
        }
        Ok(())
    }

    /// Labels the lifetime projections of `place` and its ancestors up to
    /// `frozen` for the exclusive access of `place`.
    pub(crate) fn label_rps_up_to(
        &mut self,
        place: Place<'tcx>,
        frozen: Place<'tcx>,
        reason: AdjustCapabilityReason,
    ) -> Result<(), PcgError> {
        let place_regions = place.regions(self.ctxt);
        let mut current = place;
        loop {
            self.label_rps_for_exclusive_access(current, &place_regions, reason)?;
            if current == frozen {
                return Ok(());
            }
            current = current.parent_place().unwrap();
        }
    }

    /// Labels the lifetime projections of `current` (for the regions
    /// `place_regions` of the place being accessed exclusively) that are
    /// blocked by other edges, and adds the future edges for them.
    pub(crate) fn label_rps_for_exclusive_access(
        &mut self,
        current: Place<'tcx>,
        place_regions: &IndexVec<LifetimeProjectionIdx<Region>, PcgRegion<'tcx>>,
        reason: AdjustCapabilityReason,
    ) -> Result<(), PcgError> {
        for r in place_regions {
            let Some(current_rp) = LifetimeProjection::new(
                current,
                GeneralizedLifetime::from(*r),
                None,
                self.ctxt.ctxt(),
            ) else {
                // e.g. for ReStatic
                continue;
            };
            if current.is_ref(self.ctxt)
                && !current
                    .project_deref(self.ctxt)
                    .regions(self.ctxt)
                    .iter()
                    .contains(r)
            {
                // If this region projection couldn't be modified (because its deref doesn't hold r), we skip
                // There is probably a better way to do this
                continue;
            }
            let edges_blocking_current_rp = self
                .pcg
                .borrow
                .edges_blocking(current_rp.into(), self.ctxt.bc_ctxt())
                .collect::<Vec<_>>();
            if !edges_blocking_current_rp.is_empty() {
                let labelled_rp =
                    current_rp.with_label(Some(self.prev_snapshot_location().into()), self.ctxt);
                let expansion_nodes = edges_blocking_current_rp
                    .iter()
                    .filter_map(|e| {
                        if let BorrowPcgEdgeKind::BorrowPcgExpansion(e) = e.kind()
                            && let PcgNode::LifetimeProjection(rp) = e.base()
                            && rp == current_rp.into()
                        {
                            Some(
                                e.expansion()
                                    .iter()
                                    .flat_map(|e| e.try_into_lifetime_projection())
                                    .filter(|e| e.base.is_current())
                                    .collect::<Vec<_>>(),
                            )
                        } else {
                            None
                        }
                    })
                    .flatten()
                    .collect::<HashSet<_>>();
                self.record_and_apply_action(
                    BorrowPcgAction::label_lifetime_projection(
                        LabelNodePredicate::equals_lifetime_projection(current_rp.into()),
                        Some(self.prev_snapshot_location().into()),
                        format!(
                            "{:?}: remove_read_permission_upwards_and_label_rps: label current lifetime projection {} with previous snapshot location {:?}",
                            reason,
                            current_rp.display_string(self.ctxt),
                            self.prev_snapshot_location()
                        ),
                    )
                    .into(),
                )?;
                // If the place is owned, we will never regain access to it,
                // therefore future nodes aren't necessary
                if current.as_borrowed_place(self.ctxt).is_some() {
                    let future_rp = current_rp.with_placeholder_label(self.ctxt);
                    self.record_and_apply_action(
                        BorrowPcgAction::add_edge(
                            BorrowPcgEdge::new(
                                BorrowFlowEdge::new(
                                    labelled_rp.into(),
                                    future_rp.into(),
                                    BorrowFlowEdgeKind::Future(FutureEdgeKind::ToFutureSelf),
                                )
                                .into(),
                                self.pcg.borrow.validity_conditions.clone(),
                            ),
                            "remove_read_permission_upwards_and_label_rps",
                        )
                        .into(),
                    )?;
                    for expansion_node in expansion_nodes {
                        // If the expansion isn't labelled, it is likely a sibling RO of the place gaining exclusive capability
                        // so we connect to its current version
                        // Otherwise if its labelled we connect to its placeholder version
                        let to_connect = if expansion_node.label().is_none() {
                            expansion_node.into()
                        } else {
                            expansion_node.with_placeholder_label(self.ctxt).into()
                        };
                        self.record_and_apply_action(
                            BorrowPcgAction::add_edge(
                                BorrowPcgEdge::new(
                                    BorrowFlowEdge::new(
                                        to_connect,
                                        future_rp.into(),
                                        BorrowFlowEdgeKind::Future(FutureEdgeKind::FromExpansion),
                                    )
                                    .into(),
                                    self.pcg.borrow.validity_conditions.clone(),
                                ),
                                "remove_read_permission_upwards_and_label_rps",
                            )
                            .into(),
                        )?;
                    }
                }
            }
        }
        Ok(())
    }
}

/// The reason for performing in-place updates on the PCG capabilities.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub(crate) enum AdjustCapabilityReason {
    /// Just prior to activating a two-phase borrow, the capability of the
    /// blocked place is R. The PCG evaluates the two-phase borrow by removing
    /// this capability and adjusting the capabilities of the parents of the
    /// blocked place as well as their related places. In particular, if the
    /// blocked place's parent place also has capability R, it should be removed
    /// as well.
    TwoPhaseBorrowActivation,

    /// Currently, there are situations in the analysis that require obtaining
    /// capability E to a place with capability R. In particular, consider the following code:
    /// ```rust
    /// let mut pair = (String::new(), String::new());
    /// let fst = &pair.0;
    /// let snd = pair.1;
    /// ```
    /// For the assignment to `fst`, the PCG will weaken `pair` to capability
    /// `R`, and then unpack it. Therefore, `pair.1` will have capability `R`.
    /// The assignment to `snd` requires obtaining capability `E` to `pair.1`,
    /// To handle this case, we would remove capability from `pair` and upgrade
    /// `pair.1` to `E`.
    UpgradeReadToExclusive,
}
