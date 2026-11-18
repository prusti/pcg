// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::Debug;

use crate::{
    borrow_pcg::borrow_pcg_expansion::PlaceExpansion,
    error::{PcgError, PcgUnsupportedError},
    owned_pcg::RepackGuide,
    pcg::place_capabilities::{PlaceCapabilities, PlaceCapabilitiesReader},
    rustc_interface::middle::mir::Local,
    utils::{HasCompilerCtxt, PlaceLike, SnapshotLocation, data_structures::HashSet},
};
use itertools::Itertools;

use crate::{
    pcg::CapabilityKind,
    utils::{CompilerCtxt, OwnedPlace, Place, display::DisplayWithCompilerCtxt},
};

// Former `OwnedPcgLocal` is now `pcg::owned_state::state::LocalInitState`.

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub(crate) struct ExpandedPlace<'tcx, P = Place<'tcx>> {
    pub(crate) place: P,
    pub(crate) expansion: PlaceExpansion<'tcx>,
}

impl ExpandedPlace<'_> {
    pub(crate) fn guide(&self) -> Option<RepackGuide> {
        self.expansion.guide()
    }
}

impl<'tcx, P> ExpandedPlace<'tcx, P> {
    pub(crate) fn expansion_places<Ctxt>(
        &self,
        ctxt: Ctxt,
    ) -> Result<HashSet<P>, PcgUnsupportedError>
    where
        P: PlaceLike<'tcx, Ctxt>,
    {
        Ok(self
            .place
            .expansion_places(&self.expansion, ctxt)?
            .into_iter()
            .collect())
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LocalExpansions<'tcx> {
    pub(crate) local: Local,
    pub(crate) expansions: HashSet<ExpandedPlace<'tcx>>,
}

impl<'tcx> LocalExpansions<'tcx> {
    /// Labels the `Index` guides of `index`; see [`RepackGuide::label_index`].
    pub(crate) fn label_index(&mut self, index: Local, label: SnapshotLocation) {
        if !self.expansions.iter().any(|expanded| {
            expanded
                .guide()
                .is_some_and(|guide| guide.is_unlabelled_index_of(index))
        }) {
            return;
        }
        self.expansions = std::mem::take(&mut self.expansions)
            .into_iter()
            .map(|mut expanded| {
                expanded.expansion.label_index(index, label);
                expanded
            })
            .collect();
    }

    pub(crate) fn contains_place(&self, place: Place<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        place == self.local.into() || self.contains_expansion_to(place, ctxt)
    }

    pub(crate) fn check_validity(
        &self,
        capabilities: &PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<(), String> {
        for expansion in &self.expansions {
            if capabilities.get(expansion.place, ctxt) == Some(CapabilityKind::Write) {
                return Err(format!(
                    "Base {} of expansion {:?} has write capability",
                    expansion.place.display_string(ctxt),
                    expansion
                ));
            }
        }
        Ok(())
    }
    pub(crate) fn has_expansions(&self) -> bool {
        !self.expansions.is_empty()
    }

    pub(crate) fn remove_expansion<'a>(
        &mut self,
        place: Place<'tcx>,
        guide: Option<RepackGuide>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) where
        'tcx: 'a,
    {
        tracing::debug!(
            "Removing the expansion of {} with guide {:?}",
            place.display_string(ctxt.ctxt()),
            guide
        );
        self.expansions
            .retain(|pe| pe.place != place || pe.guide() != guide);
    }

    pub(crate) fn insert_expansion(&mut self, place: Place<'tcx>, expansion: PlaceExpansion<'tcx>) {
        self.expansions.insert(ExpandedPlace { place, expansion });
    }

    /// Adds the expansions on the way to `place` that the layout lacks. It
    /// changes no capability.
    pub(crate) fn insert_layout_to<'a>(
        &mut self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Result<(), PcgError>
    where
        'tcx: 'a,
    {
        for (base, _) in place
            .iter_projections_after(self.local.into(), ctxt)
            .into_iter()
            .flatten()
        {
            let expansion = base.expand_one_level(place, ctxt)?;
            if !self.contains_expansion_to(expansion.target_place, ctxt) {
                self.insert_expansion(
                    base,
                    PlaceExpansion::from_places(expansion.expansion(), ctxt),
                );
            }
        }
        Ok(())
    }

    /// Removes the expansion to `place` and the expansions of `place` and of
    /// the places below it.
    pub(crate) fn forget_expansions_to<'a>(
        &mut self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) where
        'tcx: 'a,
    {
        self.expansions.retain(|expanded| {
            !place.is_prefix_of(expanded.place)
                && !expanded
                    .expansion_places(ctxt)
                    .is_ok_and(|places| places.contains(&place))
        });
    }

    pub(crate) fn expansions(&self) -> &HashSet<ExpandedPlace<'tcx>> {
        &self.expansions
    }

    /// The places all of whose expansions lead only to unexpanded places.
    /// These are the places that can be collapsed without first collapsing
    /// one of their descendants. A place can have several expansions, one
    /// per guide (e.g. to `a[_5]` and to `a[_8]`), and all of them count.
    pub(crate) fn places_expanded_only_to_leaves<'a>(
        &self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> HashSet<Place<'tcx>>
    where
        'tcx: 'a,
    {
        let expanded_places: HashSet<Place<'tcx>> =
            self.expansions.iter().map(|e| e.place).collect();
        expanded_places
            .iter()
            .filter(|place| {
                self.all_children_of(**place, ctxt)
                    .iter()
                    .all(|p| !expanded_places.contains(p))
            })
            .copied()
            .collect()
    }

    pub fn leaf_places<'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> HashSet<OwnedPlace<'tcx>>
    where
        'tcx: 'a,
    {
        if self.expansions.is_empty() {
            return std::iter::once(OwnedPlace::from(self.local)).collect();
        }
        self.expansions
            .iter()
            .flat_map(|e| e.expansion_places(ctxt).unwrap())
            .filter(|p| !self.contains_expansion_from(*p))
            .map(|p| {
                p.as_owned_place(ctxt)
                    .expect("owned PCG leaf places are always owned")
            })
            .collect::<HashSet<_>>()
    }

    pub fn new(local: Local) -> Self {
        Self {
            local,
            expansions: HashSet::default(),
        }
    }

    pub(crate) fn contains_expansion_from(&self, place: Place<'tcx>) -> bool {
        self.expansions.iter().any(|e| e.place == place)
    }

    pub(crate) fn expansions_from(
        &self,
        place: Place<'tcx>,
    ) -> impl Iterator<Item = &ExpandedPlace<'tcx>> {
        self.expansions.iter().filter(move |e| e.place == place)
    }

    pub(crate) fn contains_expansion_to<'a>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        self.expansions
            .iter()
            .any(|e| e.expansion_places(ctxt).unwrap().contains(&place))
    }

    pub(crate) fn places_to_collapse_for_obtain_of<'a>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Vec<Place<'tcx>>
    where
        'tcx: 'a,
    {
        if !self.contains_expansion_from(place) {
            return vec![];
        }
        let leaf_places: HashSet<Place<'tcx>> =
            self.leaf_places(ctxt).into_iter().map(Into::into).collect();
        let mut places = self
            .all_descendants_of(place, ctxt)
            .difference(&leaf_places)
            .sorted_by_key(|place| place.projection().len())
            .rev()
            .copied()
            .collect::<Vec<_>>();
        places.push(place);
        places
    }
}
