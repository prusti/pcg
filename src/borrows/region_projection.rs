use std::{fmt, marker::PhantomData};

use serde_json::json;

use crate::{
    rustc_interface::{
        ast::Mutability,
        data_structures::fx::FxHashSet,
        middle::{
            mir::{Local, PlaceElem},
            ty::{self, DebruijnIndex, RegionVid},
        },
    },
    utils::{display::DisplayWithRepacker, HasPlace, Place},
};

use crate::utils::PlaceRepacker;

use super::{
    coupling_graph_constructor::CGNode,
    domain::{MaybeOldPlace, ToJsonWithRepacker},
};
use super::{domain::MaybeRemotePlace, has_pcs_elem::HasPcsElems};

/// A region occuring in region projections
#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum PCGRegion {
    RegionVid(RegionVid),
    ReErased,
    ReStatic,
    /// TODO: Do we need this?
    ReBound(DebruijnIndex, ty::BoundRegion),
}

impl<'tcx> std::fmt::Display for PCGRegion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PCGRegion::RegionVid(vid) => write!(f, "{:?}", vid),
            PCGRegion::ReErased => write!(f, "ReErased"),
            PCGRegion::ReStatic => write!(f, "ReStatic"),
            PCGRegion::ReBound(debruijn_index, region) => {
                write!(f, "ReBound({:?}, {:?})", debruijn_index, region)
            }
        }
    }
}

impl<'tcx> From<ty::Region<'tcx>> for PCGRegion {
    fn from(region: ty::Region<'tcx>) -> Self {
        match region.kind() {
            ty::RegionKind::ReVar(vid) => PCGRegion::RegionVid(vid),
            ty::RegionKind::ReErased => PCGRegion::ReErased,
            ty::RegionKind::ReEarlyParam(_) => todo!(),
            ty::RegionKind::ReBound(debruijn_index, inner) => {
                PCGRegion::ReBound(debruijn_index, inner)
            }
            ty::RegionKind::ReLateParam(_) => todo!(),
            ty::RegionKind::ReStatic => PCGRegion::ReStatic,
            ty::RegionKind::RePlaceholder(_) => todo!(),
            ty::RegionKind::ReError(_) => todo!(),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub struct RegionProjection<'tcx, P = MaybeRemotePlace<'tcx>> {
    pub(crate) place: P,
    region: PCGRegion,
    phantom: PhantomData<&'tcx ()>,
}

impl<'tcx, T: DisplayWithRepacker<'tcx>> DisplayWithRepacker<'tcx> for RegionProjection<'tcx, T> {
    fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        format!("{}↓{}", self.place.to_short_string(repacker), self.region)
    }
}

impl<'tcx, T: ToJsonWithRepacker<'tcx>> ToJsonWithRepacker<'tcx> for RegionProjection<'tcx, T> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "place": self.place.to_json(repacker),
            "region": self.region.to_string(),
        })
    }
}

impl<'tcx, T: std::fmt::Display> fmt::Display for RegionProjection<'tcx, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}↓{}", self.place, self.region)
    }
}

impl<'tcx> RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
    pub(crate) fn project_deeper(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
        elem: PlaceElem<'tcx>,
    ) -> RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
        RegionProjection {
            place: self.place.project_deeper(repacker, elem),
            region: self.region,
            phantom: PhantomData,
        }
    }
}

impl<'tcx> From<RegionProjection<'tcx, Place<'tcx>>>
    for RegionProjection<'tcx, MaybeRemotePlace<'tcx>>
{
    fn from(rp: RegionProjection<'tcx, Place<'tcx>>) -> Self {
        RegionProjection {
            place: rp.place.into(),
            region: rp.region,
            phantom: PhantomData,
        }
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        vec![&mut self.place]
    }
}

impl<'tcx> TryFrom<CGNode<'tcx>> for RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
    type Error = ();
    fn try_from(node: CGNode<'tcx>) -> Result<Self, Self::Error> {
        match node {
            CGNode::RegionProjection(rp) => rp.try_into(),
            CGNode::RemotePlace(_) => Err(()),
        }
    }
}

impl<'tcx> TryFrom<RegionProjection<'tcx, MaybeRemotePlace<'tcx>>>
    for RegionProjection<'tcx, MaybeOldPlace<'tcx>>
{
    type Error = ();
    fn try_from(rp: RegionProjection<'tcx, MaybeRemotePlace<'tcx>>) -> Result<Self, Self::Error> {
        Ok(RegionProjection {
            place: rp.place.try_into()?,
            region: rp.region,
            phantom: PhantomData,
        })
    }
}

impl<'tcx> From<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> for RegionProjection<'tcx> {
    fn from(rp: RegionProjection<'tcx, MaybeOldPlace<'tcx>>) -> Self {
        RegionProjection {
            place: rp.place.into(),
            region: rp.region,
            phantom: PhantomData,
        }
    }
}

impl<'tcx> From<RegionProjection<'tcx, Place<'tcx>>>
    for RegionProjection<'tcx, MaybeOldPlace<'tcx>>
{
    fn from(rp: RegionProjection<'tcx, Place<'tcx>>) -> Self {
        RegionProjection {
            place: rp.place.into(),
            region: rp.region,
            phantom: PhantomData,
        }
    }
}

impl<'tcx, T> RegionProjection<'tcx, T> {
    pub(crate) fn map_place<U>(self, f: impl FnOnce(T) -> U) -> RegionProjection<'tcx, U> {
        RegionProjection {
            place: f(self.place),
            region: self.region,
            phantom: PhantomData,
        }
    }
    pub(crate) fn new(region: PCGRegion, place: T) -> Self {
        Self {
            place,
            region,
            phantom: PhantomData,
        }
    }

    pub(crate) fn region(&self) -> PCGRegion {
        self.region
    }
}

impl<'tcx> RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
    /// If the region projection is of the form `x↓'a` and `x` has type `&'a T` or `&'a mut T`,
    /// this returns `*x`.
    pub fn deref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Option<MaybeOldPlace<'tcx>> {
        if self.place.ty_region(repacker) == Some(self.region) {
            Some(self.place.project_deref(repacker))
        } else {
            None
        }
    }
}

impl<'tcx> RegionProjection<'tcx> {
    pub fn local(&self) -> Option<Local> {
        self.place.as_local_place().map(|p| p.local())
    }

    /// Returns `true` iff the place is a mutable reference, or if the place is
    /// a mutable struct. If the place is a remote place, it is mutable iff the
    /// corresponding input argument is a mutable reference.
    pub(crate) fn mutability(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Mutability {
        let place = match self.place {
            MaybeRemotePlace::Local(p) => p.place(),
            MaybeRemotePlace::Remote(rp) => rp.assigned_local().into(),
        };
        place.ref_mutability(repacker).unwrap_or_else(|| {
            if let Ok(root_place) =
                place.is_mutable(crate::utils::LocalMutationIsAllowed::Yes, repacker)
                && root_place.is_local_mutation_allowed == crate::utils::LocalMutationIsAllowed::Yes
            {
                Mutability::Mut
            } else {
                Mutability::Not
            }
        })
    }

    fn as_local_region_projection(&self) -> Option<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> {
        if let MaybeRemotePlace::Local(p) = self.place {
            Some(self.map_place(|_| p))
        } else {
            None
        }
    }

    /// If the region projection is of the form `x↓'a` and `x` has type `&'a T` or `&'a mut T`,
    /// this returns `*x`. Otherwise, it returns `None`.
    pub fn deref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Option<MaybeOldPlace<'tcx>> {
        self.as_local_region_projection()
            .and_then(|rp| rp.deref(repacker))
    }

    /// Returns the set of pairs (srp, drp) where srp ∈
    /// `source.region_projections(repacker)` and drp ∈
    /// `dest.region_projections(repacker)` and `srp.region() == drp.region()`.
    pub(crate) fn connections_between_places(
        source: MaybeOldPlace<'tcx>,
        dest: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<(
        RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
    )> {
        let mut edges = FxHashSet::default();
        for rp in source.region_projections(repacker) {
            for erp in dest.region_projections(repacker) {
                if rp.region() == erp.region() {
                    edges.insert((rp, erp));
                }
            }
        }
        edges
    }

    pub(crate) fn prefix_projection(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Option<RegionProjection<'tcx>> {
        if let MaybeRemotePlace::Local(p) = &self.place {
            let prefix = p.prefix_place(repacker)?;
            Some(RegionProjection::new(self.region, prefix.into()))
        } else {
            None
        }
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for RegionProjection<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        self.place.pcs_elems()
    }
}
