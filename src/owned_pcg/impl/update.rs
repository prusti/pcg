// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    borrow_pcg::graph::BorrowsGraph,
    owned_pcg::{LocalExpansions, OwnedPcgLocal, OwnedPcgNode},
    pcg::{
        CapabilityKind, OwnedCapability, PositiveCapability,
        place_capabilities::PlaceCapabilitiesReader,
        triple::{PlaceCondition, Triple},
    },
    pcg_validity_assert,
    utils::{
        HasBorrowCheckerCtxt, LocalMutationIsAllowed, PlaceLike, display::DisplayWithCompilerCtxt,
    },
};

use crate::rustc_interface::middle::mir::RETURN_PLACE;

use super::OwnedPcg;

impl<'tcx> OwnedPcg<'tcx> {
    fn check_pre_satisfied<'a>(
        &self,
        pre: PlaceCondition<'tcx>,
        borrows: &BorrowsGraph<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) where
        'tcx: 'a,
    {
        match pre {
            PlaceCondition::ExpandTwoPhase(_place) => {}
            PlaceCondition::Unalloc(local) => {
                pcg_validity_assert!(
                    self[local].is_unallocated(),
                    "local: {local:?}, fpcs: {self:?}\n"
                );
            }
            PlaceCondition::AllocateOrDeallocate(_local) => {}
            PlaceCondition::Capability(place, required_cap) => {
                match required_cap {
                    PositiveCapability::Read => {
                        // TODO
                    }
                    PositiveCapability::Write => {
                        // Cannot get write on a shared ref
                        pcg_validity_assert!(
                            place.is_mutable(LocalMutationIsAllowed::Yes, ctxt).is_ok()
                        );
                    }
                    PositiveCapability::Exclusive => {
                        // Cannot get exclusive on a shared ref
                        pcg_validity_assert!(
                            !place.projects_shared_ref(ctxt),
                            "Cannot get exclusive on projection of shared ref {}",
                            place.display_string(ctxt.bc_ctxt())
                        );
                    }
                    PositiveCapability::ShallowExclusive => unreachable!(),
                }
                if place.is_owned(ctxt) {
                    if self.capability(place, borrows, ctxt).is_none() {
                        pcg_validity_assert!(
                            false,
                            [ctxt],
                            "No capability for {} in {}",
                            place.display_string(ctxt.bc_ctxt()),
                            self.display_string(ctxt)
                        );
                    } else {
                        // pcg_validity_assert!(
                        //     matches!(
                        //         current_cap.partial_cmp(&required_cap),
                        //         Some(Ordering::Equal) | Some(Ordering::Greater)
                        //     ),
                        //     "Capability {current_cap:?} is not >= {required_cap:?} for {place:?}"
                        // )
                    }
                }
            }
            PlaceCondition::Return => {
                pcg_validity_assert!(
                    self.capability(RETURN_PLACE.into(), borrows, ctxt)
                        .is_exclusive()
                );
            }
            PlaceCondition::RemoveCapability(_) => unreachable!(),
        }
    }
    pub(crate) fn ensures<'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
        &mut self,
        t: Triple<'tcx>,
        borrows: &BorrowsGraph<'tcx>,
        ctxt: Ctxt,
    ) where
        'tcx: 'a,
    {
        self.check_pre_satisfied(t.pre(), borrows, ctxt);
        let Some(post) = t.post() else {
            return;
        };
        match post {
            PlaceCondition::Return => unreachable!(),
            PlaceCondition::Unalloc(local) => {
                self[local] = OwnedPcgLocal::Unallocated;
            }
            PlaceCondition::AllocateOrDeallocate(local) => {
                self[local] = OwnedPcgLocal::Allocated(LocalExpansions::new(OwnedPcgNode::leaf(
                    OwnedCapability::Write,
                )));
            }
            PlaceCondition::Capability(place, cap) => {
                if place.is_owned(ctxt) {
                    pcg_validity_assert!(
                        self.owned_subtree_mut(place, ctxt).is_some(),
                        "No owned subtree for {place:?}"
                    );
                    let Some(OwnedPcgNode::Leaf(leaf)) = self.owned_subtree_mut(place, ctxt) else {
                        return; // Validity assertion would fail
                    };
                    if cap.is_read() {
                        pcg_validity_assert!(
                            leaf.inherent_capability >= cap,
                            "Expected read capability for owned place {place:?}"
                        );
                        return;
                    }
                    if leaf.inherent_capability != cap {
                        let Some(owned_cap) = cap.into_owned_capability() else {
                            panic!("Expected owned capability for owned place {place:?}");
                        };
                        leaf.inherent_capability = owned_cap;
                    }
                }
            }
            PlaceCondition::ExpandTwoPhase(place) => {}
            PlaceCondition::RemoveCapability(place) => {}
        }
    }
}
