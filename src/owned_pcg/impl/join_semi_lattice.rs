// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    HasSettings,
    action::CapabilityChanges,
    borrow_pcg::borrow_pcg_expansion::PlaceExpansion,
    owned_pcg::{RepackCollapse, RepackExpand},
    pcg::{CapabilityKind, place_capabilities::PlaceCapabilitiesInterface},
    pcg_validity_assert, pcg_validity_expect_some,
    utils::{
        DebugCtxt, HasCompilerCtxt, Place, data_structures::HashSet,
        display::DisplayWithCompilerCtxt,
    },
};

use crate::owned_pcg::LocalExpansions;

impl<'tcx> LocalExpansions<'tcx> {
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
        let expansion_places = self.all_children_of(collapse.to, ctxt);
        let mut changes = CapabilityChanges::default();
        let retained_cap: CapabilityKind =
            expansion_places
                .iter()
                .fold(CapabilityKind::Exclusive, |acc, place| {
                    let removed_cap = place_capabilities.get(*place, ctxt);
                    changes.set(*place, None);
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
        self.remove_all_expansions_from(collapse.to, ctxt);
        changes.set(collapse.to, Some(retained_cap));
        changes.apply(place_capabilities, ctxt);
        changes
    }
}
