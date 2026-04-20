// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    HasSettings,
    pcg::{
        CapabilityKind,
        owned_state::{OwnedCapability, OwnedPcg},
        place_capabilities::{
            PlaceCapabilities, PlaceCapabilitiesInterface, PlaceCapabilitiesReader,
        },
        triple::{PlaceCondition, Triple},
    },
    pcg_validity_assert,
    utils::{HasBorrowCheckerCtxt, LocalMutationIsAllowed, display::DisplayWithCompilerCtxt},
};

use crate::rustc_interface::middle::mir::RETURN_PLACE;

impl<'tcx> OwnedPcg<'tcx> {
    fn check_pre_satisfied<'a>(
        &self,
        pre: PlaceCondition<'tcx>,
        capabilities: &PlaceCapabilities<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>,
    ) where
        'tcx: 'a,
    {
        match pre {
            PlaceCondition::ExpandTwoPhase(_place) => {}
            PlaceCondition::Unalloc(local) => {
                pcg_validity_assert!(
                    !self.is_allocated(local),
                    "local: {local:?}, owned: {self:?}\n"
                );
            }
            PlaceCondition::AllocateOrDeallocate(_local) => {}
            PlaceCondition::Capability(place, required_cap) => {
                match required_cap {
                    CapabilityKind::Read => {
                        // TODO
                    }
                    CapabilityKind::Write => {
                        pcg_validity_assert!(
                            place.is_mutable(LocalMutationIsAllowed::Yes, ctxt).is_ok()
                        );
                    }
                    CapabilityKind::Exclusive => {
                        pcg_validity_assert!(
                            !place.projects_shared_ref(ctxt),
                            "Cannot get exclusive on projection of shared ref {}",
                            place.display_string(ctxt.bc_ctxt())
                        );
                    }
                    CapabilityKind::ShallowExclusive => unreachable!(),
                }
                if place.as_owned_place(ctxt).is_some() {
                    if capabilities.get(place, ctxt).is_some() {
                    } else {
                        pcg_validity_assert!(
                            false,
                            [ctxt],
                            "No capability for {}",
                            place.display_string(ctxt.bc_ctxt())
                        );
                    }
                }
            }
            PlaceCondition::Return => {
                pcg_validity_assert!(
                    capabilities.get(RETURN_PLACE.into(), ctxt).unwrap()
                        == CapabilityKind::Exclusive,
                    [ctxt]
                );
            }
            PlaceCondition::RemoveCapability(_) => unreachable!(),
        }
    }

    /// Apply the post-condition of a [`Triple`] to this state.
    pub(crate) fn ensures<'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>>(
        &mut self,
        t: Triple<'tcx>,
        place_capabilities: &mut PlaceCapabilities<'tcx>,
        ctxt: Ctxt,
    ) where
        'tcx: 'a,
    {
        self.check_pre_satisfied(t.pre(), place_capabilities, ctxt);
        let Some(post) = t.post() else {
            return;
        };
        match post {
            PlaceCondition::Return => unreachable!(),
            PlaceCondition::Unalloc(local) => {
                self.deallocate(local);
                place_capabilities.remove_all_for_local(local, ctxt);
            }
            PlaceCondition::AllocateOrDeallocate(local) => {
                self.allocate(local, OwnedCapability::Uninit);
                place_capabilities.insert(local.into(), CapabilityKind::Write, ctxt);
            }
            PlaceCondition::Capability(place, cap) => {
                place_capabilities.insert(place, cap, ctxt);
                // It's possible that the place could have been already expanded
                // exclusively (when it could have originally been expanded for
                // read), in which case we pretend we did the right thing all
                // along
                if cap == CapabilityKind::Read {
                    for (p, _) in place_capabilities
                        .capabilities_for_strict_postfixes_of(place)
                        .collect::<Vec<_>>()
                    {
                        place_capabilities.insert(p, CapabilityKind::Read, ctxt);
                    }
                }
                if let Some(owned) = place.as_owned_place(ctxt) {
                    self.apply_capability_change(owned, cap, ctxt);
                }
            }
            PlaceCondition::ExpandTwoPhase(place) => {
                place_capabilities.insert(place, CapabilityKind::Read, ctxt);
            }
            PlaceCondition::RemoveCapability(place) => {
                place_capabilities.remove(place, ctxt);
                if let Some(owned) = place.as_owned_place(ctxt) {
                    self.remove(owned);
                }
            }
        }
    }
}
