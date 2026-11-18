// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    HasSettings,
    action::{BorrowPcgAction, CapabilityChanges, PcgAction},
    borrow_pcg::{
        action::LabelPlaceReason, borrow_pcg_expansion::PlaceExpansion, state::BorrowsStateLike,
    },
    error::PcgError,
    owned_pcg::{
        ExpandedPlace, RepackCollapse, RepackExpand, RepackOp,
        join::{data::JoinOwnedData, obtain::JoinCtxt},
    },
    pcg::{CapabilityKind, place_capabilities::PlaceCapabilitiesInterface},
    pcg_validity_assert, pcg_validity_expect_some,
    utils::{
        DebugCtxt, HasCompilerCtxt, Place, data_structures::HashSet,
        display::DisplayWithCompilerCtxt,
    },
};
use itertools::Itertools;

use crate::{
    owned_pcg::LocalExpansions,
    pcg::owned_state::{LocalInitState, OwnedPcg},
    rustc_interface::middle::mir,
};

impl<'a, 'pcg, 'tcx> JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut LocalInitState<'tcx>> {
    pub(crate) fn join(
        &mut self,
        mut other: JoinOwnedData<'a, 'pcg, 'tcx, &'pcg LocalInitState<'tcx>>,
        ctxt: JoinCtxt<'a, 'tcx>,
    ) -> Result<Vec<PcgAction<'tcx>>, PcgError> {
        match (&mut *self.owned, &mut other.owned) {
            (LocalInitState::Unallocated, LocalInitState::Unallocated) => Ok(vec![]),
            (
                LocalInitState::Allocated {
                    expansions: to_places,
                    ..
                },
                LocalInitState::Allocated {
                    expansions: from_places,
                    ..
                },
            ) => {
                let self_allocated = JoinOwnedData {
                    owned: to_places,
                    borrows: self.borrows,
                    capabilities: self.capabilities,
                    snapshot_location: self.snapshot_location,
                };
                let mut from_places = from_places.clone();
                let other_allocated = JoinOwnedData {
                    owned: &mut from_places,
                    borrows: other.borrows,
                    capabilities: other.capabilities,
                    snapshot_location: other.snapshot_location,
                };
                self_allocated.join(other_allocated, ctxt)
            }
            (LocalInitState::Allocated { expansions, .. }, LocalInitState::Unallocated) => {
                self.borrows.apply_action(
                    &mut BorrowPcgAction::label_place_and_update_related_capabilities(
                        expansions.local.into(),
                        self.snapshot_location,
                        LabelPlaceReason::StorageDead,
                    ),
                    self.capabilities,
                    ctxt,
                );
                let mut repacks = vec![];
                for (place, k) in self.capabilities.owned_capabilities(expansions.local, ctxt) {
                    if *k > CapabilityKind::Write {
                        // Temporary: mark as for_storage_dead until
                        // https://github.com/prusti/pcg/issues/137 is resolved.
                        repacks.push(
                            BorrowPcgAction::weaken_for_storage_dead(
                                place,
                                *k,
                                CapabilityKind::Write,
                                "join with a dead local",
                            )
                            .with_capabilities(vec![(place, Some(CapabilityKind::Write))].into())
                            .into(),
                        );
                        *k = CapabilityKind::Write;
                    }
                }
                repacks.extend(expansions.collapse(
                    expansions.local.into(),
                    None,
                    self.capabilities,
                    ctxt,
                ));
                repacks.push(RepackOp::StorageDead(expansions.local).into());
                *self.owned = LocalInitState::Unallocated;
                Ok(repacks)
            }
            (LocalInitState::Unallocated, LocalInitState::Allocated { expansions, .. }) => {
                other.borrows.apply_action(
                    &mut BorrowPcgAction::label_place_and_update_related_capabilities(
                        expansions.local.into(),
                        other.snapshot_location,
                        LabelPlaceReason::StorageDead,
                    ),
                    other.capabilities,
                    ctxt,
                );
                Ok(vec![])
            }
        }
    }
}

impl<'a, 'pcg, 'tcx> JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut OwnedPcg<'tcx>> {
    #[tracing::instrument(skip(self, other, ctxt), fields(self.snapshot_location = ?self.snapshot_location, other.snapshot_location = ?other.snapshot_location), level = "warn")]
    pub(crate) fn join(
        &mut self,
        mut other: JoinOwnedData<'a, 'pcg, 'tcx, &'pcg OwnedPcg<'tcx>>,
        ctxt: JoinCtxt<'a, 'tcx>,
    ) -> Result<Vec<PcgAction<'tcx>>, PcgError> {
        let mut actions = vec![];
        for local in 0..self.owned.num_locals() {
            let local: mir::Local = local.into();
            let mut owned_local_data = self.map_owned(|owned| &mut owned[local]);
            let other_owned_local_data = other.map_owned(|owned| &owned[local]);
            actions.extend(owned_local_data.join(other_owned_local_data, ctxt)?);
        }
        Ok(actions)
    }
}

impl<'tcx> LocalExpansions<'tcx> {
    pub(crate) fn expansions_shortest_first(&self) -> impl Iterator<Item = &ExpandedPlace<'tcx>> {
        self.expansions
            .iter()
            .sorted_by_key(|ep| ep.place.projection().len())
    }

    /// Performs `expand` and returns its capability changes.
    pub(crate) fn perform_expand_action<'a, Ctxt: HasCompilerCtxt<'a, 'tcx>>(
        &mut self,
        expand: RepackExpand<'tcx>,
        capabilities: &mut impl PlaceCapabilitiesInterface<'tcx>,
        ctxt: Ctxt,
    ) -> CapabilityChanges<Place<'tcx>>
    where
        'tcx: 'a,
    {
        let target_places = expand.target_places(ctxt);
        self.insert_expansion(
            expand.from,
            PlaceExpansion::from_places(target_places.clone(), ctxt).with_guide(expand.guide),
        );
        let source_cap = if expand.capability.is_read() {
            expand.capability
        } else {
            capabilities.get(expand.from, ctxt).unwrap_or_else(|| {
                pcg_validity_assert!(
                    false,
                    "no cap for {}",
                    expand.from.display_string(ctxt.ctxt())
                );
                // panic!("no cap for {}", expand.from.display_string(ctxt));
                // For debugging, assume exclusive, we can visualize the graph to see what's going on
                CapabilityKind::Exclusive
            })
        };
        let mut changes = CapabilityChanges::default();
        for target_place in target_places {
            changes.set(target_place, Some(source_cap));
        }
        changes.set(
            expand.from,
            expand.capability.is_read().then_some(CapabilityKind::Read),
        );
        changes.apply(capabilities, ctxt);
        changes
    }

    pub(crate) fn all_descendants_of<'a>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> HashSet<Place<'tcx>>
    where
        'tcx: 'a,
    {
        self.expansions
            .iter()
            .filter(|ep| place.is_prefix_of(ep.place))
            .flat_map(|ep| ep.expansion_places(ctxt).unwrap())
            .collect()
    }

    pub(crate) fn all_children_of<'a>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> HashSet<Place<'tcx>>
    where
        'tcx: 'a,
    {
        self.expansions
            .iter()
            .filter(|ep| ep.place == place)
            .flat_map(|ep| ep.expansion_places(ctxt).unwrap())
            .collect()
    }

    pub(crate) fn collapse_actions_for<'a, Ctxt: HasCompilerCtxt<'a, 'tcx>>(
        &self,
        place: Place<'tcx>,
        capabilities: &impl PlaceCapabilitiesInterface<'tcx>,
        ctxt: Ctxt,
    ) -> Vec<RepackCollapse<'tcx>>
    where
        'tcx: 'a,
    {
        self.expansions_from(place)
            .map(|expanded| {
                let cap = expanded
                    .expansion_places(ctxt)
                    .unwrap()
                    .into_iter()
                    .fold(CapabilityKind::Exclusive, |acc, child| {
                        acc.minimum(capabilities.get(child, ctxt).unwrap()).unwrap()
                    });
                RepackCollapse::new(place, cap, expanded.guide())
            })
            .collect()
    }

    /// Performs `collapse` and returns its capability changes.
    pub(crate) fn perform_collapse_action<
        'a,
        Ctxt: HasCompilerCtxt<'a, 'tcx> + DebugCtxt + HasSettings<'a>,
    >(
        &mut self,
        collapse: RepackCollapse<'tcx>,
        place_capabilities: &mut impl PlaceCapabilitiesInterface<'tcx>,
        ctxt: Ctxt,
    ) -> CapabilityChanges<Place<'tcx>>
    where
        'tcx: 'a,
    {
        // A place has one expansion per guide (e.g. one per index local), and
        // a collapse names one of them; the other expansions stay in place.
        let Some(expanded) = self
            .expansions_from(collapse.to)
            .find(|expanded| expanded.guide() == collapse.guide)
        else {
            pcg_validity_assert!(
                false,
                [ctxt],
                "Collapse {:?} names no expansion of {}",
                collapse,
                collapse.to.display_string(ctxt.ctxt())
            );
            return CapabilityChanges::default();
        };
        let expansion_places = expanded.expansion_places(ctxt).unwrap();
        self.remove_expansion(collapse.to, collapse.guide, ctxt);
        // Two expansions can have the same children (e.g. constant-index
        // expansions for different offsets). A child of an expansion that
        // remains keeps its capability.
        let children_of_remaining_expansions = self.all_children_of(collapse.to, ctxt);
        let mut changes = CapabilityChanges::default();
        let retained_cap: CapabilityKind =
            expansion_places
                .iter()
                .fold(CapabilityKind::Exclusive, |acc, place| {
                    let removed_cap = place_capabilities.get(*place, ctxt);
                    if !children_of_remaining_expansions.contains(place) {
                        changes.set(*place, None);
                    }
                    let removed_cap = pcg_validity_expect_some!(
                        removed_cap,
                        fallback: CapabilityKind::Exclusive,
                        [ctxt],
                        "Expected capability for {}",
                        place.display_string(ctxt.ctxt())
                    );
                    let joined_cap = removed_cap.minimum(acc);
                    pcg_validity_expect_some!(joined_cap,
                        fallback: CapabilityKind::Exclusive,
                        [ctxt],
                        "Cannot join capability {:?} of {} with min cap {:?}",
                        removed_cap,
                        place.display_string(ctxt.ctxt()),
                        acc
                    )
                });
        // While another expansion of `collapse.to` remains, the capability of
        // `collapse.to` stays as it is; the collapse of its last expansion
        // sets it from that expansion's children.
        if !self.contains_expansion_from(collapse.to) {
            changes.set(collapse.to, Some(retained_cap));
        }
        changes.apply(place_capabilities, ctxt);
        changes
    }
}
