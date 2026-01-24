use std::borrow::Cow;

use crate::{
    borrow_pcg::{
        has_pcs_elem::{LabelPlace, PlaceLabeller},
        region_projection::{
            HasRegions, HasTy, LifetimeProjection, PcgLifetimeProjectionBase, PcgRegion,
            PlaceOrConst, RegionIdx,
        },
        visitor::extract_regions,
    },
    error::PcgError,
    pcg::{MaybeHasLocation, PcgNode, PcgNodeLike, PcgNodeWithPlace},
    rustc_interface::{
        PlaceTy,
        index::IndexVec,
        middle::{
            mir::{self, PlaceElem},
            ty,
        },
    },
    utils::{
        CompilerCtxt, DebugCtxt, HasCompilerCtxt, HasPlace, LabelledPlace, PcgNodeComponent,
        PcgPlace, Place, PlaceProjectable, SnapshotLocation,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        json::ToJsonWithCtxt,
        maybe_remote::MaybeRemotePlace,
        validity::HasValidityCheck,
    },
};
use derive_more::From;
use serde_json::json;

#[deprecated(note = "Use MaybeLabelledPlace instead")]
pub type MaybeOldPlace<'tcx> = MaybeLabelledPlace<'tcx>;

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, From, Ord, PartialOrd)]
pub enum MaybeLabelledPlace<'tcx, P = Place<'tcx>> {
    Current(P),
    Labelled(LabelledPlace<'tcx, P>),
}

impl<'tcx, Ctxt: Copy, P: Copy + HasRegions<'tcx, Ctxt>> HasRegions<'tcx, Ctxt>
    for MaybeLabelledPlace<'tcx, P>
{
    fn regions(&self, ctxt: Ctxt) -> IndexVec<RegionIdx, PcgRegion> {
        self.place().regions(ctxt)
    }
}

impl<'tcx, Ctxt, P: PcgPlace<'tcx, Ctxt>> HasTy<'tcx, Ctxt> for MaybeLabelledPlace<'tcx, P> {
    fn rust_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx> {
        self.place().rust_ty(ctxt)
    }
}

impl<'tcx, P: Copy> MaybeLabelledPlace<'tcx, P> {
    pub(crate) fn place(self) -> P {
        match self {
            MaybeLabelledPlace::Current(place) => place,
            MaybeLabelledPlace::Labelled(labelled_place) => labelled_place.place,
        }
    }
    pub fn as_current_place(self) -> Option<P> {
        match self {
            MaybeLabelledPlace::Current(place) => Some(place),
            MaybeLabelledPlace::Labelled(_) => None,
        }
    }
}

impl<'tcx> MaybeLabelledPlace<'tcx> {
    pub fn is_mutable<'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> bool
    where
        'tcx: 'a,
    {
        self.place()
            .is_mutable(crate::utils::LocalMutationIsAllowed::Yes, ctxt)
            .is_ok()
    }
}

impl<'tcx, Ctxt, P: PcgNodeComponent> PcgNodeLike<'tcx, Ctxt, P> for MaybeLabelledPlace<'tcx, P> {
    fn to_pcg_node(self, _ctxt: Ctxt) -> PcgNodeWithPlace<'tcx, P> {
        PcgNode::Place(self.into())
    }
}
impl<'tcx, Ctxt, P: PcgNodeComponent> PcgNodeLike<'tcx, Ctxt, P> for LabelledPlace<'tcx, P> {
    fn to_pcg_node(self, _ctxt: Ctxt) -> PcgNodeWithPlace<'tcx, P> {
        PcgNode::Place(self.into())
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

impl<'a, 'tcx: 'a, Ctxt: DebugCtxt + HasCompilerCtxt<'a, 'tcx>> HasValidityCheck<Ctxt>
    for MaybeLabelledPlace<'tcx>
{
    fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
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

impl<'tcx, Ctxt: Copy, P: PlaceProjectable<'tcx, Ctxt> + PcgNodeComponent> PlaceProjectable<'tcx, Ctxt>
    for MaybeLabelledPlace<'tcx, P>
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

impl<'tcx, P: Copy> HasPlace<'tcx, P> for MaybeLabelledPlace<'tcx, P> {
    fn place(&self) -> P {
        match self {
            MaybeLabelledPlace::Current(place) => *place,
            MaybeLabelledPlace::Labelled(labelled_place) => labelled_place.place,
        }
    }
    fn place_mut(&mut self) -> &mut P {
        match self {
            MaybeLabelledPlace::Current(place) => place,
            MaybeLabelledPlace::Labelled(labelled_place) => &mut labelled_place.place,
        }
    }

    fn is_place(&self) -> bool {
        true
    }
}

impl<'a, 'tcx: 'a, Ctxt, P: Copy + DisplayWithCtxt<Ctxt>> DisplayWithCtxt<Ctxt>
    for MaybeLabelledPlace<'tcx, P>
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

impl<P> MaybeHasLocation for MaybeLabelledPlace<'_, P> {
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

    #[allow(dead_code)]
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

    #[allow(dead_code)]
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

impl<'tcx, Ctxt> LabelPlace<'tcx, Ctxt> for MaybeLabelledPlace<'tcx> {
    fn label_place(&mut self, labeller: &impl PlaceLabeller<'tcx, Ctxt>, ctxt: Ctxt) -> bool {
        match self {
            MaybeLabelledPlace::Current(place) => {
                let label = labeller.place_label(*place, ctxt);
                *self = MaybeLabelledPlace::Labelled(LabelledPlace::new(*place, label));
                true
            }
            MaybeLabelledPlace::Labelled(_) => false,
        }
    }
}
