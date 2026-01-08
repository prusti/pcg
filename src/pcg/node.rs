use crate::{
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        domain::LoopAbstractionInput,
        edge_data::{LabelNodePredicate, NodeReplacement},
        graph::loop_abstraction::MaybeRemoteCurrentPlace,
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionResult, LabelNodeContext, LabelPlace,
            PlaceLabeller,
        },
        region_projection::{
            LifetimeProjection, LifetimeProjectionLabel, PcgLifetimeProjectionBase,
            PcgLifetimeProjectionBaseLike, PlaceOrConst,
        },
    },
    rustc_interface::middle::mir,
    utils::{
        CompilerCtxt, HasCompilerCtxt, Place, SnapshotLocation,
        data_structures::HashSet,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        json::ToJsonWithCtxt,
        maybe_old::MaybeLabelledPlace,
        place::maybe_remote::MaybeRemotePlace,
        validity::HasValidityCheck,
    },
};

#[deprecated(note = "Use `PcgNode` instead")]
pub type PCGNode<'tcx> = PcgNode<'tcx>;

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum PcgNodeType {
    Place,
    LifetimeProjection,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum PcgNode<'tcx, T = MaybeLabelledPlace<'tcx>, U = PcgLifetimeProjectionBase<'tcx>> {
    Place(T),
    LifetimeProjection(LifetimeProjection<'tcx, U>),
}

impl<'tcx, T: LabelPlace<'tcx>, U: LabelPlace<'tcx>> LabelPlace<'tcx> for PcgNode<'tcx, T, U> {
    fn label_place(
        &mut self,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        match self {
            PcgNode::Place(p) => p.label_place(labeller, ctxt),
            PcgNode::LifetimeProjection(rp) => rp.base.label_place(labeller, ctxt),
        }
    }
}

impl<'tcx> PcgNode<'tcx> {
    pub fn related_place(self) -> Option<MaybeRemotePlace<'tcx>> {
        match self {
            PcgNode::Place(p) => Some(p.into()),
            PcgNode::LifetimeProjection(rp) => match rp.base() {
                PlaceOrConst::Place(p) => Some(p),
                _ => None,
            },
        }
    }

    pub fn related_maybe_labelled_place(self) -> Option<MaybeLabelledPlace<'tcx>> {
        self.related_place().and_then(|p| p.as_local_place())
    }

    pub(crate) fn related_maybe_remote_current_place(
        &self,
    ) -> Option<MaybeRemoteCurrentPlace<'tcx>> {
        match self {
            PcgNode::Place(p) => match p {
                MaybeLabelledPlace::Current(place) => Some(MaybeRemoteCurrentPlace::Local(*place)),
                MaybeLabelledPlace::Labelled(_) => None,
            },
            PcgNode::LifetimeProjection(rp) => rp.base().maybe_remote_current_place(),
        }
    }
}

impl<'tcx, T, U> PcgNode<'tcx, T, U> {
    pub(crate) fn is_place(&self) -> bool {
        matches!(self, PcgNode::Place(_))
    }

    pub fn expect_lifetime_projection(self) -> LifetimeProjection<'tcx, U> {
        match self {
            PcgNode::LifetimeProjection(rp) => rp,
            _ => panic!(),
        }
    }

    pub(crate) fn try_into_lifetime_projection(self) -> Result<LifetimeProjection<'tcx, U>, Self> {
        match self {
            PcgNode::LifetimeProjection(rp) => Ok(rp),
            _ => Err(self),
        }
    }
}

impl<'tcx> From<LoopAbstractionInput<'tcx>> for PcgNode<'tcx> {
    fn from(target: LoopAbstractionInput<'tcx>) -> Self {
        target.0
    }
}

impl<'tcx, T, U: Copy + PcgLifetimeProjectionBaseLike<'tcx>> LabelLifetimeProjection<'tcx>
    for PcgNode<'tcx, T, U>
where
    PcgLifetimeProjectionBase<'tcx>: From<U>,
{
    fn label_lifetime_projection(
        &mut self,
        label: Option<LifetimeProjectionLabel>,
    ) -> LabelLifetimeProjectionResult {
        if let PcgNode::LifetimeProjection(this_projection) = self {
            this_projection.label_lifetime_projection(label)
        } else {
            LabelLifetimeProjectionResult::Unchanged
        }
    }
}

impl<T, U> From<T> for PcgNode<'_, T, U> {
    fn from(value: T) -> Self {
        PcgNode::Place(value)
    }
}

impl<'tcx, U> From<LifetimeProjection<'tcx, U>> for PcgNode<'tcx, MaybeRemotePlace<'tcx>, U> {
    fn from(value: LifetimeProjection<'tcx, U>) -> Self {
        PcgNode::LifetimeProjection(value)
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, Place<'tcx>>> for PcgNode<'tcx> {
    fn from(value: LifetimeProjection<'tcx, Place<'tcx>>) -> Self {
        PcgNode::LifetimeProjection(value.into())
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>> for PcgNode<'tcx> {
    fn from(value: LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>) -> Self {
        PcgNode::LifetimeProjection(value.into())
    }
}

impl<'tcx, T: PcgNodeLike<'tcx>, U: PcgLifetimeProjectionBaseLike<'tcx>> PcgNodeLike<'tcx>
    for PcgNode<'tcx, T, U>
{
    fn node_type(&self) -> PcgNodeType {
        match self {
            PcgNode::Place(_) => PcgNodeType::Place,
            PcgNode::LifetimeProjection(_) => PcgNodeType::LifetimeProjection,
        }
    }

    fn to_pcg_node<C: Copy>(self, ctxt: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx> {
        match self {
            PcgNode::Place(p) => p.to_pcg_node(ctxt),
            PcgNode::LifetimeProjection(rp) => rp.to_pcg_node(ctxt),
        }
    }
}

impl<'a, 'tcx, T: HasValidityCheck<'a, 'tcx>, U: PcgLifetimeProjectionBaseLike<'tcx>>
    HasValidityCheck<'a, 'tcx> for PcgNode<'tcx, T, U>
where
    LifetimeProjection<'tcx, U>: HasValidityCheck<'a, 'tcx>,
{
    fn check_validity(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> Result<(), String> {
        match self {
            PcgNode::Place(p) => p.check_validity(ctxt),
            PcgNode::LifetimeProjection(rp) => rp.check_validity(ctxt),
        }
    }
}

impl<
    'tcx,
    Ctxt,
    T: PcgNodeLike<'tcx> + DisplayWithCtxt<Ctxt>,
    U: PcgLifetimeProjectionBaseLike<'tcx> + DisplayWithCtxt<Ctxt>,
> DisplayWithCtxt<Ctxt> for PcgNode<'tcx, T, U>
where
    LifetimeProjection<'tcx, U>: DisplayWithCtxt<Ctxt>,
{
    fn display_output(&self, ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(
            match self {
                PcgNode::Place(p) => p.display_string(ctxt),
                PcgNode::LifetimeProjection(rp) => rp.display_string(ctxt),
            }
            .into(),
        )
    }
}

impl<'tcx, T, U, Ctxt> ToJsonWithCtxt<Ctxt> for PcgNode<'tcx, T, U> {
    fn to_json(&self, _ctxt: Ctxt) -> serde_json::Value {
        todo!()
    }
}

pub trait MaybeHasLocation {
    fn location(&self) -> Option<SnapshotLocation>;
}

impl<'tcx, T: MaybeHasLocation, U: PcgLifetimeProjectionBaseLike<'tcx> + MaybeHasLocation>
    MaybeHasLocation for PcgNode<'tcx, T, U>
{
    fn location(&self) -> Option<SnapshotLocation> {
        match self {
            PcgNode::Place(place) => place.location(),
            PcgNode::LifetimeProjection(region_projection) => region_projection.base().location(),
        }
    }
}

pub trait PcgNodeLike<'tcx>:
    Clone + Copy + std::fmt::Debug + Eq + PartialEq + std::hash::Hash
{
    fn to_pcg_node<C: Copy>(self, ctxt: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx>;

    fn node_type(&self) -> PcgNodeType;

    fn try_to_local_node<'a>(self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> Option<LocalNode<'tcx>>
    where
        'tcx: 'a,
    {
        match self.to_pcg_node(ctxt.ctxt()) {
            PcgNode::Place(p) => Some(p.into()),
            PcgNode::LifetimeProjection(rp) => match rp.base() {
                PlaceOrConst::Place(maybe_remote_place) => match maybe_remote_place {
                    MaybeRemotePlace::Local(maybe_old_place) => {
                        Some(rp.with_base(maybe_old_place).to_local_node(ctxt.ctxt()))
                    }
                    MaybeRemotePlace::Remote(_) => None,
                },
                PlaceOrConst::Const(_) => None,
            },
        }
    }
}

pub(crate) trait LabelPlaceConditionally<'tcx>:
    PcgNodeLike<'tcx> + LabelPlace<'tcx>
{
    fn label_place_conditionally(
        &mut self,
        replacements: &mut HashSet<NodeReplacement<'tcx>>,
        predicate: &LabelNodePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        node_context: LabelNodeContext,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) {
        let orig = self.to_pcg_node(ctxt);
        if predicate.applies_to(orig, node_context) {
            let changed = self.label_place(labeller, ctxt);
            if changed {
                replacements.insert(NodeReplacement::new(orig, self.to_pcg_node(ctxt)));
            }
        }
    }
}

impl<'tcx, T: PcgNodeLike<'tcx> + LabelPlace<'tcx>> LabelPlaceConditionally<'tcx> for T {}

pub(crate) trait LocalNodeLike<'tcx>: Copy + PcgNodeLike<'tcx> {
    fn to_local_node<C: Copy>(self, ctxt: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx>;
}

impl<'tcx> LocalNodeLike<'tcx> for mir::Place<'tcx> {
    fn to_local_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx> {
        LocalNode::Place(self.into())
    }
}

impl<'tcx> PcgNodeLike<'tcx> for mir::Place<'tcx> {
    fn to_pcg_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx> {
        self.into()
    }

    fn node_type(&self) -> PcgNodeType {
        PcgNodeType::Place
    }
}
