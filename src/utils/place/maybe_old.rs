use crate::borrow_pcg::borrow_pcg_edge::LocalNode;
use crate::borrow_pcg::has_pcs_elem::HasPcgElems;
use crate::borrow_pcg::latest::Latest;
use crate::borrow_pcg::region_projection::{
    MaybeRemoteRegionProjectionBase, PCGRegion, RegionIdx, RegionProjection,
    RegionProjectionBaseLike,
};
use crate::borrow_pcg::visitor::extract_regions;
use crate::combined_pcs::{LocalNodeLike, MaybeHasLocation, PCGNode, PCGNodeLike, PcgError};
use crate::rustc_interface::index::{Idx, IndexVec};
use crate::rustc_interface::middle::mir;
use crate::rustc_interface::middle::mir::tcx::PlaceTy;
use crate::rustc_interface::middle::mir::PlaceElem;
use crate::utils::display::DisplayWithRepacker;
use crate::utils::json::ToJsonWithRepacker;
use crate::utils::maybe_remote::MaybeRemotePlace;
use crate::utils::validity::HasValidityCheck;
use crate::utils::{HasPlace, Place, PlaceRepacker, PlaceSnapshot, SnapshotLocation};
use derive_more::From;
use serde_json::json;

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, From, Ord, PartialOrd)]
pub enum MaybeOldPlace<'tcx> {
    Current { place: Place<'tcx> },
    OldPlace(PlaceSnapshot<'tcx>),
}

impl<'tcx> LocalNodeLike<'tcx> for MaybeOldPlace<'tcx> {
    fn to_local_node(self, repacker: PlaceRepacker<'_, 'tcx>) -> LocalNode<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => place.to_local_node(repacker),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.to_local_node(repacker),
        }
    }
}

impl<'tcx> RegionProjectionBaseLike<'tcx> for MaybeOldPlace<'tcx> {
    fn to_maybe_remote_region_projection_base(&self) -> MaybeRemoteRegionProjectionBase<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => place.to_maybe_remote_region_projection_base(),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.to_maybe_remote_region_projection_base(),
        }
    }

    fn regions(&self, repacker: PlaceRepacker<'_, 'tcx>) -> IndexVec<RegionIdx, PCGRegion> {
        match self {
            MaybeOldPlace::Current { place } => place.regions(repacker),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.place.regions(repacker),
        }
    }
}

impl<'tcx> PCGNodeLike<'tcx> for MaybeOldPlace<'tcx> {
    fn to_pcg_node(self, repacker: PlaceRepacker<'_, 'tcx>) -> PCGNode<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => place.to_pcg_node(repacker),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.to_pcg_node(repacker),
        }
    }
}

impl<'tcx> TryFrom<MaybeRemoteRegionProjectionBase<'tcx>> for MaybeOldPlace<'tcx> {
    type Error = ();

    fn try_from(value: MaybeRemoteRegionProjectionBase<'tcx>) -> Result<Self, Self::Error> {
        match value {
            MaybeRemoteRegionProjectionBase::Place(maybe_remote_place) => {
                maybe_remote_place.try_into()
            }
            MaybeRemoteRegionProjectionBase::Const(_) => Err(()),
        }
    }
}

impl<'tcx> HasValidityCheck<'tcx> for MaybeOldPlace<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        match self {
            MaybeOldPlace::Current { place } => place.check_validity(repacker),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.check_validity(repacker),
        }
    }
}

impl<'tcx> ToJsonWithRepacker<'tcx> for MaybeOldPlace<'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        match self {
            MaybeOldPlace::Current { place } => place.to_json(repacker),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.to_json(repacker),
        }
    }
}

impl<'tcx> TryFrom<PCGNode<'tcx>> for MaybeOldPlace<'tcx> {
    type Error = ();
    fn try_from(node: PCGNode<'tcx>) -> Result<Self, Self::Error> {
        match node {
            PCGNode::Place(p) => Ok(p.try_into()?),
            PCGNode::RegionProjection(_) => Err(()),
        }
    }
}

impl<'tcx> TryFrom<MaybeRemotePlace<'tcx>> for MaybeOldPlace<'tcx> {
    type Error = ();
    fn try_from(remote_place: MaybeRemotePlace<'tcx>) -> Result<Self, Self::Error> {
        match remote_place {
            MaybeRemotePlace::Local(p) => Ok(p),
            MaybeRemotePlace::Remote(_) => Err(()),
        }
    }
}

impl From<mir::Local> for MaybeOldPlace<'_> {
    fn from(local: mir::Local) -> Self {
        Self::Current {
            place: local.into(),
        }
    }
}

impl<'tcx> From<mir::Place<'tcx>> for MaybeOldPlace<'tcx> {
    fn from(place: mir::Place<'tcx>) -> Self {
        Self::Current {
            place: place.into(),
        }
    }
}

impl std::fmt::Display for MaybeOldPlace<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MaybeOldPlace::Current { place } => write!(f, "{:?}", place),
            MaybeOldPlace::OldPlace(old_place) => write!(f, "{}", old_place),
        }
    }
}

impl<'tcx> HasPlace<'tcx> for MaybeOldPlace<'tcx> {
    fn place(&self) -> Place<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => *place,
            MaybeOldPlace::OldPlace(old_place) => old_place.place,
        }
    }
    fn place_mut(&mut self) -> &mut Place<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => place,
            MaybeOldPlace::OldPlace(old_place) => &mut old_place.place,
        }
    }

    fn project_deeper(
        &self,
        elem: PlaceElem<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Result<Self, PcgError> {
        let mut cloned = *self;
        *cloned.place_mut() = self
            .place()
            .project_deeper(elem, repacker)
            .map_err(PcgError::unsupported)?;
        Ok(cloned)
    }

    fn iter_projections(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<(Self, PlaceElem<'tcx>)> {
        match self {
            MaybeOldPlace::Current { place } => place
                .iter_projections(repacker)
                .into_iter()
                .map(|(p, e)| (p.into(), e))
                .collect(),
            MaybeOldPlace::OldPlace(old_place) => old_place
                .place
                .iter_projections(repacker)
                .into_iter()
                .map(|(p, e)| (p.into(), e))
                .collect(),
        }
    }
}

impl<'tcx> DisplayWithRepacker<'tcx> for MaybeOldPlace<'tcx> {
    fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        let p = self.place().to_short_string(repacker);
        format!(
            "{}{}",
            p,
            if let Some(location) = self.location() {
                format!(" at {:?}", location)
            } else {
                "".to_string()
            }
        )
    }
}

impl MaybeHasLocation for MaybeOldPlace<'_> {
    fn location(&self) -> Option<SnapshotLocation> {
        match self {
            MaybeOldPlace::Current { .. } => None,
            MaybeOldPlace::OldPlace(old_place) => Some(old_place.at),
        }
    }
}
impl<'tcx> MaybeOldPlace<'tcx> {
    pub(crate) fn with_location(self, location: SnapshotLocation) -> Self {
        MaybeOldPlace::new(self.place(), Some(location))
    }

    pub fn is_old(&self) -> bool {
        matches!(self, MaybeOldPlace::OldPlace(_))
    }

    pub fn projection(&self) -> &'tcx [PlaceElem<'tcx>] {
        self.place().projection
    }

    pub(crate) fn deref_to_rp(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Option<RegionProjection<'tcx, Self>> {
        if let Some((place, PlaceElem::Deref)) = self.last_projection() {
            place.base_region_projection(repacker)
        } else {
            None
        }
    }

    pub(crate) fn base_region_projection(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Option<RegionProjection<'tcx, Self>> {
        self.place()
            .base_region_projection(repacker)
            .map(|rp| rp.with_base(*self, repacker))
    }

    pub(crate) fn is_owned(&self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        self.place().is_owned(repacker)
    }

    pub(crate) fn local(&self) -> mir::Local {
        self.place().local
    }

    pub(crate) fn ty_region(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Option<PCGRegion> {
        self.place().ty_region(repacker)
    }

    pub fn last_projection(&self) -> Option<(MaybeOldPlace<'tcx>, PlaceElem<'tcx>)> {
        match self {
            MaybeOldPlace::Current { place } => place.last_projection().map(|(p, e)| (p.into(), e)),
            MaybeOldPlace::OldPlace(snapshot) => snapshot
                .place
                .last_projection()
                .map(|(p, e)| (PlaceSnapshot::new(p, snapshot.at).into(), e)),
        }
    }

    pub(crate) fn with_inherent_region(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> MaybeOldPlace<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => place.with_inherent_region(repacker).into(),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.with_inherent_region(repacker).into(),
        }
    }

    pub(crate) fn region_projection(
        &self,
        idx: RegionIdx,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> RegionProjection<'tcx, Self> {
        let region_projections = self.region_projections(repacker);
        if idx.index() < region_projections.len() {
            region_projections[idx.index()]
        } else {
            panic!(
                "Region projection index {:?} out of bounds for place {:?}, ty: {:?}",
                idx,
                self,
                self.ty(repacker)
            );
        }
    }

    pub(crate) fn region_projections(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<RegionProjection<'tcx, Self>> {
        let place = self.with_inherent_region(repacker);
        extract_regions(place.ty(repacker).ty, repacker)
            .iter()
            .map(|region| RegionProjection::new(*region, place, repacker).unwrap())
            .collect()
    }

    pub fn new<T: Into<SnapshotLocation>>(place: Place<'tcx>, at: Option<T>) -> Self {
        if let Some(at) = at {
            Self::OldPlace(PlaceSnapshot::new(place, at))
        } else {
            Self::Current { place }
        }
    }

    pub fn ty(&self, repacker: PlaceRepacker<'_, 'tcx>) -> PlaceTy<'tcx> {
        self.place().ty(repacker)
    }

    pub(crate) fn project_deref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> MaybeOldPlace<'tcx> {
        MaybeOldPlace::new(self.place().project_deref(repacker), self.location())
    }

    pub fn is_current(&self) -> bool {
        matches!(self, MaybeOldPlace::Current { .. })
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "place": self.place().to_json(repacker),
            "at": self.location().map(|loc| format!("{:?}", loc)),
        })
    }

    pub(crate) fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest<'tcx>) -> bool {
        if self.is_current() && (place.is_prefix(self.place()) || self.place().is_prefix(place)) {
            *self = MaybeOldPlace::OldPlace(PlaceSnapshot {
                place: self.place(),
                at: latest.get(self.place()),
            });
            true
        } else {
            false
        }
    }
}

impl<'tcx> HasPcgElems<Place<'tcx>> for MaybeOldPlace<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut Place<'tcx>> {
        match self {
            MaybeOldPlace::Current { place } => vec![place],
            MaybeOldPlace::OldPlace(snapshot) => snapshot.pcg_elems(),
        }
    }
}
