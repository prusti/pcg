use std::borrow::Cow;

use crate::{
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        edge_data::LabelPlacePredicate,
        has_pcs_elem::{LabelNodeContext, LabelPlaceWithContext, PlaceLabeller},
        region_projection::{
            HasRegions, HasTy, LifetimeProjection, PcgLifetimeProjectionBase, PcgRegion,
            PlaceOrConst, RegionIdx,
        },
        visitor::extract_regions,
    },
    error::PcgError,
    pcg::{LocalNodeLike, MaybeHasLocation, PcgNode, PcgNodeLike},
    rustc_interface::{
        PlaceTy,
        index::IndexVec,
        middle::{
            mir::{self, PlaceElem},
            ty,
        },
    },
    utils::{
        CompilerCtxt, HasCompilerCtxt, HasPlace, LabelledPlace, Place, PlaceProjectable,
        SnapshotLocation,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        json::ToJsonWithCtxt,
        maybe_remote::MaybeRemotePlace,
        validity::HasValidityCheck,
    },
};
use derive_more::{From, TryInto};
use serde_json::json;

#[deprecated(note = "Use MaybeLabelledPlace instead")]
pub type MaybeOldPlace<'tcx> = MaybeLabelledPlace<'tcx>;

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, From, Ord, PartialOrd, TryInto)]
pub enum MaybeLabelledPlace<'tcx> {
    Current(Place<'tcx>),
    Labelled(LabelledPlace<'tcx>),
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> HasRegions<'tcx, Ctxt>
    for MaybeLabelledPlace<'tcx>
{
    fn regions(&self, ctxt: Ctxt) -> IndexVec<RegionIdx, PcgRegion> {
        self.place().regions(ctxt)
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> HasTy<'tcx, Ctxt> for MaybeLabelledPlace<'tcx> {
    fn rust_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx> {
        self.place().ty(ctxt).ty
    }
}

impl<'tcx> MaybeLabelledPlace<'tcx> {
    pub fn as_current_place(self) -> Option<Place<'tcx>> {
        match self {
            MaybeLabelledPlace::Current(place) => Some(place),
            MaybeLabelledPlace::Labelled(_) => None,
        }
    }

    pub fn is_mutable<'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> bool
    where
        'tcx: 'a,
    {
        self.place()
            .is_mutable(crate::utils::LocalMutationIsAllowed::Yes, ctxt)
            .is_ok()
    }
}

impl<'tcx> LocalNodeLike<'tcx> for MaybeLabelledPlace<'tcx> {
    fn to_local_node<C: Copy>(self, ctxt: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx> {
        match self {
            MaybeLabelledPlace::Current(place) => place.to_local_node(ctxt),
            MaybeLabelledPlace::Labelled(snapshot) => snapshot.to_local_node(ctxt),
        }
    }
}

impl<'tcx> PcgNodeLike<'tcx> for MaybeLabelledPlace<'tcx> {
    fn to_pcg_node<C: Copy>(self, ctxt: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx> {
        match self {
            MaybeLabelledPlace::Current(place) => place.to_pcg_node(ctxt),
            MaybeLabelledPlace::Labelled(snapshot) => snapshot.to_pcg_node(ctxt),
        }
    }
}

impl<'tcx> TryFrom<PcgLifetimeProjectionBase<'tcx>> for MaybeLabelledPlace<'tcx> {
    type Error = String;

    fn try_from(value: PcgLifetimeProjectionBase<'tcx>) -> Result<Self, Self::Error> {
        match value {
            PlaceOrConst::Place(maybe_remote_place) => maybe_remote_place.try_into(),
            PlaceOrConst::Const(_) => {
                Err("Const cannot be converted to a maybe old place".to_owned())
            }
        }
    }
}

impl<'tcx> HasValidityCheck<'_, 'tcx> for MaybeLabelledPlace<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        match self {
            MaybeLabelledPlace::Current(place) => place.check_validity(ctxt),
            MaybeLabelledPlace::Labelled(snapshot) => snapshot.check_validity(ctxt),
        }
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> ToJsonWithCtxt<Ctxt>
    for MaybeLabelledPlace<'tcx>
{
    fn to_json(&self, ctxt: Ctxt) -> serde_json::Value {
        match self {
            MaybeLabelledPlace::Current(place) => place.to_json(ctxt),
            MaybeLabelledPlace::Labelled(snapshot) => snapshot.to_json(ctxt),
        }
    }
}

impl<'tcx> TryFrom<PcgNode<'tcx>> for MaybeLabelledPlace<'tcx> {
    type Error = String;
    fn try_from(node: PcgNode<'tcx>) -> Result<Self, Self::Error> {
        match node {
            PcgNode::Place(p) => Ok(p),
            PcgNode::LifetimeProjection(_) => {
                Err("Lifetime projection cannot be converted to a maybe labelled place".to_owned())
            }
        }
    }
}

impl<'tcx> TryFrom<MaybeRemotePlace<'tcx>> for MaybeLabelledPlace<'tcx> {
    type Error = String;
    fn try_from(remote_place: MaybeRemotePlace<'tcx>) -> Result<Self, Self::Error> {
        match remote_place {
            MaybeRemotePlace::Local(p) => Ok(p),
            MaybeRemotePlace::Remote(r) => Err(format!(
                "Remote place {r:?} cannot be converted to a maybe old place"
            )),
        }
    }
}

impl From<mir::Local> for MaybeLabelledPlace<'_> {
    fn from(local: mir::Local) -> Self {
        Self::Current(local.into())
    }
}

impl<'tcx> From<mir::Place<'tcx>> for MaybeLabelledPlace<'tcx> {
    fn from(place: mir::Place<'tcx>) -> Self {
        Self::Current(place.into())
    }
}

impl std::fmt::Display for MaybeLabelledPlace<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MaybeLabelledPlace::Current(place) => write!(f, "{place:?}"),
            MaybeLabelledPlace::Labelled(old_place) => write!(f, "{old_place}"),
        }
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> PlaceProjectable<'tcx, Ctxt>
    for MaybeLabelledPlace<'tcx>
{
    fn project_deeper(&self, elem: PlaceElem<'tcx>, ctxt: Ctxt) -> Result<Self, PcgError> {
        Ok(match self {
            MaybeLabelledPlace::Current(place) => {
                MaybeLabelledPlace::Current(place.project_deeper(elem, ctxt)?)
            }
            MaybeLabelledPlace::Labelled(old_place) => {
                MaybeLabelledPlace::Labelled(old_place.project_deeper(elem, ctxt)?)
            }
        })
    }

    fn iter_projections(&self, ctxt: Ctxt) -> Vec<(Self, PlaceElem<'tcx>)> {
        match self {
            MaybeLabelledPlace::Current(place) => place
                .iter_projections(ctxt)
                .into_iter()
                .map(|(p, e)| (p.into(), e))
                .collect(),
            MaybeLabelledPlace::Labelled(old_place) => old_place
                .place
                .iter_projections(ctxt)
                .into_iter()
                .map(|(p, e)| (p.into(), e))
                .collect(),
        }
    }
}

impl<'tcx> HasPlace<'tcx> for MaybeLabelledPlace<'tcx> {
    fn place(&self) -> Place<'tcx> {
        match self {
            MaybeLabelledPlace::Current(place) => *place,
            MaybeLabelledPlace::Labelled(old_place) => old_place.place,
        }
    }
    fn place_mut(&mut self) -> &mut Place<'tcx> {
        match self {
            MaybeLabelledPlace::Current(place) => place,
            MaybeLabelledPlace::Labelled(old_place) => &mut old_place.place,
        }
    }

    fn is_place(&self) -> bool {
        true
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for MaybeLabelledPlace<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        let location_part = if let Some(location) = self.location() {
            DisplayOutput::Seq(vec![
                DisplayOutput::Text(Cow::Borrowed(" ")),
                location.display_output((), mode),
            ])
        } else {
            DisplayOutput::Text(Cow::Borrowed(""))
        };
        DisplayOutput::Seq(vec![self.place().display_output(ctxt, mode), location_part])
    }
}

impl MaybeHasLocation for MaybeLabelledPlace<'_> {
    fn location(&self) -> Option<SnapshotLocation> {
        match self {
            MaybeLabelledPlace::Current(_) => None,
            MaybeLabelledPlace::Labelled(old_place) => Some(old_place.at),
        }
    }
}
impl<'tcx> MaybeLabelledPlace<'tcx> {
    pub fn is_old(&self) -> bool {
        matches!(self, MaybeLabelledPlace::Labelled(_))
    }

    pub fn projection(&self) -> &'tcx [PlaceElem<'tcx>] {
        self.place().projection
    }

    pub(crate) fn deref_to_rp<C: Copy>(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> Option<LifetimeProjection<'tcx, Self>> {
        if let Some((place, PlaceElem::Deref)) = self.last_projection() {
            place.base_lifetime_projection(ctxt)
        } else {
            None
        }
    }

    pub(crate) fn base_lifetime_projection<'a>(
        &self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Option<LifetimeProjection<'tcx, Self>>
    where
        'tcx: 'a,
    {
        self.place()
            .base_lifetime_projection(ctxt)
            .map(|rp| rp.with_base(*self))
    }

    pub(crate) fn is_owned<C: Copy>(&self, ctxt: CompilerCtxt<'_, 'tcx, C>) -> bool {
        self.place().is_owned(ctxt)
    }

    pub(crate) fn local(&self) -> mir::Local {
        self.place().local
    }

    pub(crate) fn ty_region(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Option<PcgRegion> {
        self.place().ty_region(ctxt)
    }

    pub fn last_projection(&self) -> Option<(MaybeLabelledPlace<'tcx>, PlaceElem<'tcx>)> {
        match self {
            MaybeLabelledPlace::Current(place) => {
                place.last_projection().map(|(p, e)| (p.into(), e))
            }
            MaybeLabelledPlace::Labelled(snapshot) => snapshot
                .place
                .last_projection()
                .map(|(p, e)| (LabelledPlace::new(p, snapshot.at).into(), e)),
        }
    }

    pub(crate) fn with_inherent_region<'a>(
        &self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> MaybeLabelledPlace<'tcx>
    where
        'tcx: 'a,
    {
        match self {
            MaybeLabelledPlace::Current(place) => place.with_inherent_region(ctxt).into(),
            MaybeLabelledPlace::Labelled(snapshot) => snapshot.with_inherent_region(ctxt).into(),
        }
    }

    pub(crate) fn lifetime_projections<'a>(
        &self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Vec<LifetimeProjection<'tcx, Self>>
    where
        'tcx: 'a,
    {
        let place = self.with_inherent_region(ctxt);
        extract_regions(place.ty(ctxt).ty)
            .iter()
            .map(|region| LifetimeProjection::new(place, *region, None, ctxt.ctxt()).unwrap())
            .collect()
    }

    pub fn new<T: Into<SnapshotLocation>>(place: Place<'tcx>, at: Option<T>) -> Self {
        if let Some(at) = at {
            Self::Labelled(LabelledPlace::new(place, at))
        } else {
            Self::Current(place)
        }
    }

    pub fn ty<'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> PlaceTy<'tcx>
    where
        'tcx: 'a,
    {
        self.place().ty(ctxt)
    }

    pub(crate) fn project_deref<BC: Copy>(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> MaybeLabelledPlace<'tcx> {
        MaybeLabelledPlace::new(self.place().project_deref(ctxt), self.location())
    }

    pub fn is_current(&self) -> bool {
        matches!(self, MaybeLabelledPlace::Current { .. })
    }

    pub fn to_json<BC: Copy>(&self, ctxt: CompilerCtxt<'_, 'tcx, BC>) -> serde_json::Value {
        json!({
            "place": self.place().to_json(ctxt),
            "at": self.location().map(|loc| format!("{loc:?}")),
        })
    }
}

impl<'tcx> LabelPlaceWithContext<'tcx, LabelNodeContext> for MaybeLabelledPlace<'tcx> {
    fn label_place_with_context(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        label_context: LabelNodeContext,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        match self {
            MaybeLabelledPlace::Current(place) => {
                if predicate.applies_to(*place, label_context, ctxt) {
                    *self = MaybeLabelledPlace::Labelled(LabelledPlace::new(
                        *place,
                        labeller.place_label(*place, ctxt),
                    ));
                    true
                } else {
                    false
                }
            }
            _ => false,
        }
    }
}
