// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::cmp::Reverse;

use crate::{
    HasSettings,
    borrow_pcg::{action::LabelPlaceReason, has_pcs_elem::SetLabel, state::BorrowsStateLike},
    error::{PcgError, PcgInternalError},
    owned_pcg::{
        ExpandedPlace, LocalExpansions, RepackOp,
        join::data::JoinOwnedData,
        traverse::{GetExpansions, Traversable},
    },
    utils::{
        HasBorrowCheckerCtxt, HasCompilerCtxt, OwnedPlace, Place, SnapshotLocation, data_structures::HashSet
    },
};
use itertools::Itertools;

use crate::{
    owned_pcg::{OwnedPcg, OwnedPcgLocal, OwnedPcgNode},
    rustc_interface::middle::mir,
};

impl<'a, 'pcg, 'tcx> JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut LocalExpansions<'tcx>> {
    #[allow(clippy::unnecessary_wraps, clippy::needless_pass_by_value)]
    pub(crate) fn join(
        &mut self,
        local: mir::Local,
        other: JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut LocalExpansions<'tcx>>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError<'tcx>>
    where
        'tcx: 'a,
    {
        Ok(self.owned.join(local, other.owned, ctxt))
    }
}
impl<'a, 'pcg, 'tcx> JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut OwnedPcgLocal<'tcx>> {
    #[tracing::instrument(skip(self, other, ctxt), fields(self.block = ?self.block, other.block = ?other.block), level = "warn")]
    pub(crate) fn join(
        &mut self,
        local: mir::Local,
        mut other: JoinOwnedData<'a, 'pcg, 'tcx, &'pcg OwnedPcgLocal<'tcx>>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError<'tcx>>
    where
        'tcx: 'a,
    {
        match (&mut self.owned, &mut other.owned) {
            (OwnedPcgLocal::Unallocated, OwnedPcgLocal::Unallocated) => Ok(vec![]),
            (OwnedPcgLocal::Allocated(to_places), OwnedPcgLocal::Allocated(from_places)) => {
                let mut self_allocated = JoinOwnedData {
                    owned: to_places,
                    borrows: self.borrows,
                    block: self.block,
                };
                let mut from_places = from_places.clone();
                let other_allocated = JoinOwnedData {
                    owned: &mut from_places,
                    borrows: other.borrows,
                    block: other.block,
                };
                self_allocated.join(local, other_allocated, ctxt)
            }
            (OwnedPcgLocal::Allocated(expansions), OwnedPcgLocal::Unallocated) => {
                self.borrows.label_place(
                    local.into(),
                    LabelPlaceReason::StorageDead,
                    &SetLabel(SnapshotLocation::before_block(self.block)),
                    ctxt,
                );
                let mut repacks = expansions
                    .collapse(local.into(), ctxt)
                    .map(|r| r.ops)
                    .unwrap_or_default();
                repacks.push(RepackOp::StorageDead(local.into()));
                *self.owned = OwnedPcgLocal::Unallocated;
                Ok(repacks)
            }
            (OwnedPcgLocal::Unallocated, OwnedPcgLocal::Allocated(_expansions)) => {
                other.borrows.label_place(
                    local.into(),
                    LabelPlaceReason::StorageDead,
                    &SetLabel(SnapshotLocation::before_block(self.block)),
                    ctxt,
                );
                Ok(vec![])
            }
        }
    }
}

impl<'a, 'pcg, 'tcx> JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut OwnedPcg<'tcx>> {
    pub(crate) fn join(
        &mut self,
        mut other: JoinOwnedData<'a, 'pcg, 'tcx, &'pcg OwnedPcg<'tcx>>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError<'tcx>>
    where
        'tcx: 'a,
    {
        let mut actions = vec![];
        for local in 0..self.owned.num_locals() {
            let local: mir::Local = local.into();
            let mut owned_local_data = self.map_owned(|owned| owned.get_mut(local).unwrap());
            let other_owned_local_data = other.map_owned(|owned| owned.get(local).unwrap());
            actions.extend(owned_local_data.join(local, other_owned_local_data, ctxt)?);
        }
        Ok(actions)
    }
}

impl<'tcx> OwnedPcgNode<'tcx> {
    pub(crate) fn expansions_longest_first<'a>(
        &self,
        base_place: OwnedPlace<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Result<Vec<ExpandedPlace<'tcx>>, PcgInternalError>
    where
        'tcx: 'a,
    {
        Ok(self
            .traverse_result(base_place, &mut GetExpansions::new(), ctxt)?
            .into_iter()
            .sorted_by_key(|e| Reverse(e.place.projection.len()))
            .collect())
    }

    pub(crate) fn all_children_of<'a>(
        &self,
        place: OwnedPlace<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> HashSet<Place<'tcx>>
    where
        'tcx: 'a,
    {
        match self.find_subtree(place.projection).subtree() {
            Some(subtree) => subtree.leaf_places(place, ctxt),
            None => HashSet::default(),
        }
    }
}
