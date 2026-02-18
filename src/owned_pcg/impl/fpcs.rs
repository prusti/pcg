// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::{Debug, Formatter, Result};

use crate::{
    borrow_pcg::graph::BorrowsGraph,
    owned_pcg::OwnedPcgNode,
    pcg::{
        CapabilityKind, CapabilityLike, OwnedCapability, PositiveCapability,
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesReader},
    },
    rustc_interface::{
        index::{Idx, IndexVec},
        middle::mir::{self, Local, RETURN_PLACE},
    },
    utils::{DebugCtxt, HasCompilerCtxt, HasLocals, Place, PlaceLike, data_structures::HashSet},
};
use derive_more::{Deref, DerefMut};

use crate::{owned_pcg::OwnedPcgLocal, utils::CompilerCtxt};

#[derive(Clone, PartialEq, Eq, Deref, DerefMut)]
/// The expansions of all locals.
pub struct OwnedPcg<'tcx>(IndexVec<Local, OwnedPcgLocal<'tcx>>);

impl Debug for OwnedPcg<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let v: Vec<_> = self.0.iter().filter(|c| !c.is_unallocated()).collect();
        v.fmt(f)
    }
}

impl<'tcx> OwnedPcg<'tcx> {
    pub(crate) fn owned_subtree_mut<'a>(
        &mut self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Option<&mut OwnedPcgNode<'tcx>>
    where
        'tcx: 'a,
    {
        assert!(place.is_owned(ctxt));
        let owned_local = &mut self.0[place.local];
        if let OwnedPcgLocal::Allocated(expansions) = owned_local {
            expansions.subtree_mut(&place.projection)
        } else {
            None
        }
    }
    pub(crate) fn owned_subtree<'a>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Option<&OwnedPcgNode<'tcx>>
    where
        'tcx: 'a,
    {
        assert!(place.is_owned(ctxt));
        let owned_local = &self.0[place.local];
        if let OwnedPcgLocal::Allocated(expansions) = owned_local {
            expansions.subtree(&place.projection)
        } else {
            None
        }
    }
    pub(crate) fn capability<'a>(
        &self,
        place: Place<'tcx>,
        borrows: &BorrowsGraph<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx> + DebugCtxt,
    ) -> CapabilityKind
    where
        'tcx: 'a,
    {
        if place.is_owned(ctxt) {
            let Some(owned_subtree) = self.owned_subtree(place, ctxt) else {
                return CapabilityKind::None(());
            };
            let mut capability: CapabilityKind = owned_subtree.inherent_capability().into();
            for borrow_place in borrows.places(ctxt) {
                if place.is_prefix_of(borrow_place) {
                    let borrow_capability = borrows.capability(borrow_place, ctxt).unwrap();
                    capability = capability.minimum(borrow_capability.into(), ctxt);
                }
            }
            capability
        } else {
            borrows
                .capability(place, ctxt)
                .map(|c| c.into())
                .unwrap_or(CapabilityKind::None(()))
        }
    }
    pub(crate) fn start_block<Ctxt: HasLocals>(ctxt: Ctxt) -> Self {
        let always_live = ctxt.always_live_locals();
        let return_local = RETURN_PLACE;
        let last_arg = Local::new(ctxt.arg_count());
        let capability_summary = IndexVec::from_fn_n(
            |local: mir::Local| {
                if local == return_local {
                    OwnedPcgLocal::new(OwnedCapability::Write)
                } else if local <= last_arg {
                    OwnedPcgLocal::new(OwnedCapability::Exclusive)
                } else if always_live.contains(local) {
                    OwnedPcgLocal::new(OwnedCapability::Write)
                } else {
                    // Other locals are unallocated
                    OwnedPcgLocal::Unallocated
                }
            },
            ctxt.local_count(),
        );
        OwnedPcg(capability_summary)
    }
}

impl<'tcx> OwnedPcg<'tcx> {
    pub(crate) fn check_validity<'a>(
        &self,
        borrows: &BorrowsGraph<'tcx>,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> std::result::Result<(), String> {
        self.0
            .iter()
            .try_for_each(|c| c.check_validity(borrows, ctxt))
    }

    pub(crate) fn num_locals(&self) -> usize {
        self.0.len()
    }

    pub(crate) fn leaf_places<'a>(
        &self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> HashSet<Place<'tcx>>
    where
        'tcx: 'a,
    {
        self.0
            .iter_enumerated()
            .filter(|(_, c)| !c.is_unallocated())
            .flat_map(|(local, c)| c.get_allocated().leaf_places(local.into(), ctxt))
            .collect()
    }

    pub(crate) fn contains_place(&self, place: Place<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        let expansion = &self.0[place.local];
        if expansion.is_unallocated() {
            return false;
        }
        expansion
            .get_allocated()
            .contains_projection_to(&place.projection)
    }

    pub(crate) fn is_allocated(&self, local: Local) -> bool {
        !self.0[local].is_unallocated()
    }

    pub(crate) fn allocated_locals(&self) -> Vec<mir::Local> {
        self.0
            .iter_enumerated()
            .filter_map(|(i, c)| if c.is_unallocated() { None } else { Some(i) })
            .collect()
    }

    pub(crate) fn unallocated_locals(&self) -> Vec<mir::Local> {
        self.0
            .iter_enumerated()
            .filter_map(|(i, c)| if c.is_unallocated() { Some(i) } else { None })
            .collect()
    }
}
