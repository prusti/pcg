// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    borrow_pcg::graph::BorrowsGraph,
    owned_pcg::{LocalExpansions, OwnedPcgLocal, OwnedPcgNode},
    pcg::{
        OwnedCapability,
        triple::{PlacePostcondition, PlacePrecondition, Triple},
    },
    utils::HasBorrowCheckerCtxt,
};

use super::OwnedPcg;

impl<'tcx> OwnedPcg<'tcx> {
    #[allow(clippy::unused_self)]
    fn check_pre_satisfied<'a>(
        &self,
        _pre: &PlacePrecondition<'tcx>,
        _borrows: &BorrowsGraph<'tcx>,
        _ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) where
        'tcx: 'a,
    {
    }
    pub(crate) fn ensures<'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
        &mut self,
        t: &Triple<'tcx>,
        borrows: &BorrowsGraph<'tcx>,
        ctxt: Ctxt,
    ) where
        'tcx: 'a,
    {
        self.check_pre_satisfied(t.pre(), borrows, ctxt);
        match t.post() {
            PlacePostcondition::Unalloc(local) => {
                self[local] = OwnedPcgLocal::Unallocated;
            }
            PlacePostcondition::Alloc(local) => {
                self[local] = OwnedPcgLocal::Allocated(LocalExpansions::new(OwnedPcgNode::leaf(
                    OwnedCapability::Uninitialized,
                )));
            }
            PlacePostcondition::Capability(place, cap) => {
                if let Some(place) = place.as_owned_place(ctxt)
                    && let Some(OwnedPcgNode::Leaf(leaf)) = self.owned_subtree_mut(place)
                {
                    leaf.capability = cap;
                }
            }
            PlacePostcondition::True => {}
        }
    }
}
