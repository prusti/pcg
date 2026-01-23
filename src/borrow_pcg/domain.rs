use derive_more::{Deref, DerefMut, From};

use super::region_projection::LifetimeProjection;
use crate::{
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionResult, LabelPlace, PlaceLabeller,
            label_lifetime_projection_wrapper, label_place_wrapper,
        },
        region_projection::{
            LifetimeProjectionLabel, LocalLifetimeProjection, OverrideRegionDebugString,
            PcgLifetimeProjectionBase, PcgLifetimeProjectionBaseLike, PcgLifetimeProjectionLike,
            PlaceOrConst,
        },
    },
    pcg::{PcgNode, PcgNodeLike, PcgNodeWithPlace, pcg_node_like_wrapper},
    utils::{
        CompilerCtxt, DebugCtxt, HasBorrowCheckerCtxt, PcgPlace, Place,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode, display_with_ctxt_node_wrapper},
        place::maybe_old::MaybeLabelledPlace,
        validity::{HasValidityCheck, has_validity_check_node_wrapper},
    },
};

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref, DerefMut)]
pub struct FunctionCallAbstractionInput<'tcx, P = Place<'tcx>>(
    pub(crate) LifetimeProjection<'tcx, PlaceOrConst<'tcx, MaybeLabelledPlace<'tcx, P>>>,
);

impl<'tcx> LifetimeProjection<'tcx, PlaceOrConst<'tcx, MaybeLabelledPlace<'tcx>>> {
    pub fn try_to_local_lifetime_projection(self) -> Option<LocalLifetimeProjection<'tcx>> {
        match self.base {
            PlaceOrConst::Place(maybe_labelled_place) => Some(self.with_base(maybe_labelled_place)),
            PlaceOrConst::Const(_) => None,
        }
    }
}

impl<'tcx, P, T: PcgLifetimeProjectionBaseLike<'tcx, P>>
    PcgLifetimeProjectionLike<'tcx, PcgLifetimeProjectionBase<'tcx, P>>
    for LifetimeProjection<'tcx, T>
{
    fn to_pcg_lifetime_projection(
        self,
    ) -> LifetimeProjection<'tcx, PcgLifetimeProjectionBase<'tcx, P>> {
        self.with_base(self.base.to_pcg_lifetime_projection_base())
    }
}

label_lifetime_projection_wrapper!(FunctionCallAbstractionInput<'tcx, P>);
label_place_wrapper!(FunctionCallAbstractionInput<'tcx, P>);
pcg_node_like_wrapper!(FunctionCallAbstractionInput<'tcx, P>);
has_validity_check_node_wrapper!(FunctionCallAbstractionInput<'tcx, P>);
display_with_ctxt_node_wrapper!(FunctionCallAbstractionInput<'tcx, P>);

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref, DerefMut)]
pub struct LoopAbstractionInput<'tcx, P = Place<'tcx>>(pub(crate) PcgNodeWithPlace<'tcx, P>);

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref, DerefMut)]
pub struct LoopAbstractionOutput<'tcx, P = Place<'tcx>>(pub(crate) LocalNode<'tcx, P>);

impl<'tcx> From<MaybeLabelledPlace<'tcx>> for LoopAbstractionInput<'tcx> {
    fn from(value: MaybeLabelledPlace<'tcx>) -> Self {
        LoopAbstractionInput(value.into())
    }
}

impl<'tcx> LoopAbstractionOutput<'tcx> {
    pub(crate) fn to_abstraction_output(self) -> AbstractionOutputTarget<'tcx> {
        AbstractionOutputTarget(self.0)
    }
}

label_lifetime_projection_wrapper!(LoopAbstractionInput<'tcx, P>);

impl<'tcx, Ctxt> LabelPlace<'tcx, Ctxt> for LoopAbstractionInput<'tcx> {
    fn label_place(&mut self, labeller: &impl PlaceLabeller<'tcx, Ctxt>, ctxt: Ctxt) -> bool {
        self.0.label_place(labeller, ctxt)
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx> + OverrideRegionDebugString>
    DisplayWithCtxt<Ctxt> for LoopAbstractionInput<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> crate::utils::display::DisplayOutput {
        self.0.display_output(ctxt, mode)
    }
}

pcg_node_like_wrapper!(LoopAbstractionInput<'tcx, P>);
has_validity_check_node_wrapper!(LoopAbstractionInput<'tcx, P>);

impl<'tcx, P: Copy> From<LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx, P>>>
    for LoopAbstractionInput<'tcx, P>
{
    fn from(value: LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx, P>>) -> Self {
        LoopAbstractionInput(PcgNode::LifetimeProjection(value.rebase()))
    }
}

impl<'tcx> TryFrom<LoopAbstractionInput<'tcx>> for LifetimeProjection<'tcx> {
    type Error = ();

    fn try_from(value: LoopAbstractionInput<'tcx>) -> Result<Self, Self::Error> {
        match value.0 {
            PcgNode::LifetimeProjection(rp) => Ok(rp),
            _ => Err(()),
        }
    }
}

label_lifetime_projection_wrapper!(LoopAbstractionOutput<'tcx, P>);
label_place_wrapper!(LoopAbstractionOutput<'tcx, P>);

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for LoopAbstractionOutput<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> crate::utils::display::DisplayOutput {
        self.0.display_output(ctxt, mode)
    }
}

pcg_node_like_wrapper!(LoopAbstractionOutput<'tcx, P>);

impl<'a, 'tcx> HasValidityCheck<CompilerCtxt<'a, 'tcx>> for LoopAbstractionOutput<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> Result<(), String> {
        self.0.check_validity(ctxt)
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>>
    for LoopAbstractionOutput<'tcx>
{
    fn from(value: LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>) -> Self {
        LoopAbstractionOutput(PcgNode::LifetimeProjection(value))
    }
}

impl<'tcx> TryFrom<LoopAbstractionOutput<'tcx>> for LifetimeProjection<'tcx> {
    type Error = ();

    fn try_from(value: LoopAbstractionOutput<'tcx>) -> Result<Self, Self::Error> {
        match value.0 {
            PcgNode::LifetimeProjection(rp) => Ok(rp.into()),
            _ => Err(()),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref)]
pub struct AbstractionInputTarget<'tcx, P = Place<'tcx>>(pub(crate) PcgNodeWithPlace<'tcx, P>);

impl<'tcx, Ctxt, P: PcgPlace<'tcx, Ctxt>> PcgNodeLike<'tcx, Ctxt, P>
    for AbstractionInputTarget<'tcx, P>
{
    fn to_pcg_node(self, _ctxt: Ctxt) -> PcgNodeWithPlace<'tcx, P> {
        self.0
    }
}

impl<'tcx, Ctxt: Copy + DebugCtxt, P> HasValidityCheck<Ctxt> for AbstractionInputTarget<'tcx, P>
where
    PcgNodeWithPlace<'tcx, P>: HasValidityCheck<Ctxt>,
{
    fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
        self.0.check_validity(ctxt)
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref, DerefMut)]
pub struct AbstractionOutputTarget<'tcx, P = Place<'tcx>>(pub(crate) LocalNode<'tcx, P>);

label_place_wrapper!(AbstractionOutputTarget<'tcx, P>);
label_lifetime_projection_wrapper!(AbstractionOutputTarget<'tcx, P>);
has_validity_check_node_wrapper!(AbstractionOutputTarget<'tcx, P>);
display_with_ctxt_node_wrapper!(AbstractionOutputTarget<'tcx, P>);

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref, DerefMut)]
pub struct FunctionCallAbstractionOutput<'tcx, P = Place<'tcx>>(
    pub(crate) LocalLifetimeProjection<'tcx, P>,
);

impl<'tcx> From<LifetimeProjection<'tcx, Place<'tcx>>> for FunctionCallAbstractionOutput<'tcx> {
    fn from(value: LifetimeProjection<'tcx, Place<'tcx>>) -> Self {
        FunctionCallAbstractionOutput(value.into())
    }
}

display_with_ctxt_node_wrapper!(FunctionCallAbstractionOutput<'tcx, P>);
pcg_node_like_wrapper!(FunctionCallAbstractionOutput<'tcx, P>);
has_validity_check_node_wrapper!(FunctionCallAbstractionOutput<'tcx, P>);
label_lifetime_projection_wrapper!(FunctionCallAbstractionOutput<'tcx, P>);
label_place_wrapper!(FunctionCallAbstractionOutput<'tcx, P>);

impl<'tcx> PcgLifetimeProjectionLike<'tcx> for FunctionCallAbstractionOutput<'tcx> {
    fn to_pcg_lifetime_projection(self) -> LifetimeProjection<'tcx> {
        self.0.to_pcg_lifetime_projection()
    }
}
