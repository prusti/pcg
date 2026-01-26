use crate::{
    HasCompilerCtxt,
    borrow_pcg::{
        graph::loop_abstraction::MaybeRemoteCurrentPlace,
        has_pcs_elem::{LabelPlace, PlaceLabeller},
        region_projection::{
            HasTy, PcgLifetimeProjectionBase, PcgLifetimeProjectionBaseLike, PlaceOrConst,
        },
    },
    rustc_interface::middle::{mir, ty},
    utils::{
        CompilerCtxt, HasPlace, LabelledPlace, PcgPlace, Place,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        json::ToJsonWithCtxt,
        place::{maybe_old::MaybeLabelledPlace, remote::RemotePlace},
    },
};

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash, PartialOrd, Ord)]
pub enum MaybeRemotePlace<'tcx, P = Place<'tcx>> {
    /// A place that has a name in the program
    Local(MaybeLabelledPlace<'tcx, P>),

    /// A place that cannot be named, e.g. the source of a reference-type input argument
    Remote(RemotePlace),
}

impl<'tcx, P> From<RemotePlace> for MaybeRemotePlace<'tcx, P> {
    fn from(place: RemotePlace) -> Self {
        MaybeRemotePlace::Remote(place)
    }
}

impl<'tcx, P> From<MaybeLabelledPlace<'tcx, P>> for MaybeRemotePlace<'tcx, P> {
    fn from(place: MaybeLabelledPlace<'tcx, P>) -> Self {
        MaybeRemotePlace::Local(place)
    }
}

impl<'tcx, Ctxt> LabelPlace<'tcx, Ctxt> for MaybeRemotePlace<'tcx> {
    fn label_place(&mut self, labeller: &impl PlaceLabeller<'tcx, Ctxt>, ctxt: Ctxt) -> bool {
        match self {
            MaybeRemotePlace::Local(p) => p.label_place(labeller, ctxt),
            MaybeRemotePlace::Remote(_) => false,
        }
    }
}

impl<'tcx> MaybeRemotePlace<'tcx> {
    pub fn is_remote(self) -> bool {
        matches!(self, MaybeRemotePlace::Remote(_))
    }

    pub(crate) fn maybe_remote_current_place(&self) -> Option<MaybeRemoteCurrentPlace<'tcx>> {
        match self {
            MaybeRemotePlace::Local(MaybeLabelledPlace::Current(place)) => {
                Some(MaybeRemoteCurrentPlace::Local(*place))
            }
            MaybeRemotePlace::Local(MaybeLabelledPlace::Labelled(_)) => None,
            MaybeRemotePlace::Remote(rp) => Some(MaybeRemoteCurrentPlace::Remote(*rp)),
        }
    }

    pub(crate) fn is_mutable<'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> bool
    where
        'tcx: 'a,
    {
        match self {
            MaybeRemotePlace::Local(p) => p.is_mutable(ctxt),
            MaybeRemotePlace::Remote(_) => false,
        }
    }
}

impl<'tcx> TryFrom<PcgLifetimeProjectionBase<'tcx>> for MaybeRemotePlace<'tcx> {
    type Error = ();
    fn try_from(value: PcgLifetimeProjectionBase<'tcx>) -> Result<Self, Self::Error> {
        match value {
            PlaceOrConst::Place(maybe_remote_place) => Ok(maybe_remote_place),
            PlaceOrConst::Const(_) => Err(()),
        }
    }
}

impl<'tcx, Ctxt, P: PcgPlace<'tcx, Ctxt>> HasTy<'tcx, Ctxt> for MaybeRemotePlace<'tcx, P>
where
    RemotePlace: HasTy<'tcx, Ctxt>,
{
    fn rust_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx> {
        match self {
            MaybeRemotePlace::Local(p) => p.rust_ty(ctxt),
            MaybeRemotePlace::Remote(rp) => rp.rust_ty(ctxt),
        }
    }
}

impl<'tcx, P: PcgLifetimeProjectionBaseLike<'tcx, P>> PcgLifetimeProjectionBaseLike<'tcx, P>
    for MaybeRemotePlace<'tcx, P>
{
    fn to_pcg_lifetime_projection_base(&self) -> PcgLifetimeProjectionBase<'tcx, P> {
        match self {
            MaybeRemotePlace::Local(p) => p.to_pcg_lifetime_projection_base(),
            MaybeRemotePlace::Remote(rp) => (*rp).into(),
        }
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for MaybeRemotePlace<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        match self {
            MaybeRemotePlace::Local(p) => p.display_output(ctxt, mode),
            MaybeRemotePlace::Remote(rp) => DisplayOutput::Text(format!("{rp}").into()),
        }
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> ToJsonWithCtxt<Ctxt>
    for MaybeRemotePlace<'tcx>
{
    fn to_json(&self, ctxt: Ctxt) -> serde_json::Value {
        match self {
            MaybeRemotePlace::Local(p) => p.to_json(ctxt.ctxt()),
            MaybeRemotePlace::Remote(rp) => format!("{rp}").into(),
        }
    }
}

impl std::fmt::Display for MaybeRemotePlace<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MaybeRemotePlace::Local(p) => write!(f, "{p}"),
            MaybeRemotePlace::Remote(l) => write!(f, "Remote({l:?})"),
        }
    }
}

impl<'tcx, P: Copy> MaybeRemotePlace<'tcx, P> {
    pub fn as_current_place(&self) -> Option<P> {
        match self {
            MaybeRemotePlace::Local(p) => p.as_current_place(),
            MaybeRemotePlace::Remote(_) => None,
        }
    }

    pub fn as_local_place(&self) -> Option<MaybeLabelledPlace<'tcx, P>> {
        match self {
            MaybeRemotePlace::Local(p) => Some(*p),
            MaybeRemotePlace::Remote(_) => None,
        }
    }
}

impl<'tcx> MaybeRemotePlace<'tcx> {
    pub fn place_assigned_to_local(local: mir::Local) -> Self {
        MaybeRemotePlace::Remote(RemotePlace { local })
    }

    pub(crate) fn related_local_place(&self) -> Place<'tcx> {
        match self {
            MaybeRemotePlace::Local(p) => p.place(),
            MaybeRemotePlace::Remote(rp) => rp.local.into(),
        }
    }

    pub(crate) fn as_local_place_mut(&mut self) -> Option<&mut MaybeLabelledPlace<'tcx>> {
        match self {
            MaybeRemotePlace::Local(p) => Some(p),
            MaybeRemotePlace::Remote(_) => None,
        }
    }

    pub fn to_json(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> serde_json::Value {
        match self {
            MaybeRemotePlace::Local(p) => p.to_json(ctxt),
            MaybeRemotePlace::Remote(_) => todo!(),
        }
    }
}

impl<'tcx> From<LabelledPlace<'tcx>> for MaybeRemotePlace<'tcx> {
    fn from(place: LabelledPlace<'tcx>) -> Self {
        MaybeRemotePlace::Local(place.into())
    }
}

impl<'tcx> From<Place<'tcx>> for MaybeRemotePlace<'tcx> {
    fn from(place: Place<'tcx>) -> Self {
        MaybeRemotePlace::Local(place.into())
    }
}

impl<'tcx> From<mir::Place<'tcx>> for MaybeRemotePlace<'tcx> {
    fn from(place: mir::Place<'tcx>) -> Self {
        MaybeRemotePlace::Local(place.into())
    }
}

impl RemotePlace {
    pub fn new(local: mir::Local) -> Self {
        Self { local }
    }

    pub fn assigned_local(self) -> mir::Local {
        self.local
    }
}
