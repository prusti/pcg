use derive_more::{Deref, DerefMut, From};

use super::region_projection::LifetimeProjection;
use crate::{
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionResult, LabelPlace, PlaceLabeller,
        },
        region_projection::{
            LifetimeProjectionLabel, LocalLifetimeProjection, OverrideRegionDebugString,
            PcgLifetimeProjectionBaseLike, PcgLifetimeProjectionLike, PlaceOrConst,
        },
    },
    pcg::{PcgNode, PcgNodeLike},
    utils::{
        CompilerCtxt, HasBorrowCheckerCtxt, Place,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        place::maybe_old::MaybeLabelledPlace,
        validity::HasValidityCheck,
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

impl<'tcx, P: Copy> LabelLifetimeProjection<'tcx>
    for PcgNode<'tcx, MaybeLabelledPlace<'tcx, P>, PlaceOrConst<'tcx, MaybeLabelledPlace<'tcx, P>>>
where
    LifetimeProjection<'tcx, PlaceOrConst<'tcx, MaybeLabelledPlace<'tcx, P>>>:
        LabelLifetimeProjection<'tcx>,
{
    fn label_lifetime_projection(
        &mut self,
        label: Option<LifetimeProjectionLabel>,
    ) -> LabelLifetimeProjectionResult {
        match self {
            PcgNode::LifetimeProjection(rp) => rp.label_lifetime_projection(label),
            PcgNode::Place(_) => LabelLifetimeProjectionResult::Unchanged,
        }
    }
}

impl<'tcx, T: PcgLifetimeProjectionBaseLike<'tcx>> PcgLifetimeProjectionLike<'tcx>
    for LifetimeProjection<'tcx, T>
{
    fn to_pcg_lifetime_projection(self) -> LifetimeProjection<'tcx> {
        self.with_base(self.base.to_pcg_lifetime_projection_base())
    }
}

impl<'tcx, P> LabelLifetimeProjection<'tcx> for FunctionCallAbstractionInput<'tcx, P>
where
    LifetimeProjection<'tcx, PlaceOrConst<'tcx, MaybeLabelledPlace<'tcx, P>>>:
        LabelLifetimeProjection<'tcx>,
{
    fn label_lifetime_projection(
        &mut self,
        label: Option<LifetimeProjectionLabel>,
    ) -> LabelLifetimeProjectionResult {
        self.0.label_lifetime_projection(label)
    }
}

impl<'tcx, Ctxt, P> LabelPlace<'tcx, Ctxt, P> for FunctionCallAbstractionInput<'tcx, P>
where
    PlaceOrConst<'tcx, MaybeLabelledPlace<'tcx, P>>: LabelPlace<'tcx, Ctxt, P>,
{
    fn label_place(&mut self, labeller: &impl PlaceLabeller<'tcx, Ctxt, P>, ctxt: Ctxt) -> bool {
        self.0.base.label_place(labeller, ctxt)
    }
}

impl<'tcx, Ctxt> PcgNodeLike<'tcx, Ctxt> for FunctionCallAbstractionInput<'tcx> {
    fn to_pcg_node(self, ctxt: Ctxt) -> PcgNode<'tcx> {
        self.0.to_pcg_node(ctxt)
    }
}

impl<'a, 'tcx> HasValidityCheck<CompilerCtxt<'a, 'tcx>> for FunctionCallAbstractionInput<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> Result<(), String> {
        self.0.check_validity(ctxt)
    }
}

impl<'tcx, Ctxt> DisplayWithCtxt<Ctxt> for FunctionCallAbstractionInput<'tcx>
where
    LifetimeProjection<'tcx, PlaceOrConst<'tcx, MaybeLabelledPlace<'tcx>>>: DisplayWithCtxt<Ctxt>,
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        self.0.display_output(ctxt, mode)
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref)]
pub struct LoopAbstractionInput<'tcx>(pub(crate) PcgNode<'tcx>);

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref)]
pub struct LoopAbstractionOutput<'tcx>(pub(crate) LocalNode<'tcx>);

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

impl<'tcx> LabelLifetimeProjection<'tcx> for LoopAbstractionInput<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        label: Option<LifetimeProjectionLabel>,
    ) -> LabelLifetimeProjectionResult {
        self.0.label_lifetime_projection(label)
    }
}

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

impl<'tcx, Ctxt> PcgNodeLike<'tcx, Ctxt> for LoopAbstractionInput<'tcx> {
    fn to_pcg_node(self, _ctxt: Ctxt) -> PcgNode<'tcx> {
        self.0
    }
}

impl<'a, 'tcx> HasValidityCheck<CompilerCtxt<'a, 'tcx>> for LoopAbstractionInput<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> Result<(), String> {
        self.0.check_validity(ctxt)
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>> for LoopAbstractionInput<'tcx> {
    fn from(value: LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>) -> Self {
        LoopAbstractionInput(PcgNode::LifetimeProjection(value.into()))
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

impl<'tcx> LabelLifetimeProjection<'tcx> for LoopAbstractionOutput<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        label: Option<LifetimeProjectionLabel>,
    ) -> LabelLifetimeProjectionResult {
        self.0.label_lifetime_projection(label)
    }
}

impl<'tcx, Ctxt> LabelPlace<'tcx, Ctxt> for LoopAbstractionOutput<'tcx> {
    fn label_place(&mut self, labeller: &impl PlaceLabeller<'tcx, Ctxt>, ctxt: Ctxt) -> bool {
        self.0.label_place(labeller, ctxt)
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for LoopAbstractionOutput<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> crate::utils::display::DisplayOutput {
        self.0.display_output(ctxt, mode)
    }
}

impl<'tcx, Ctxt> PcgNodeLike<'tcx, Ctxt> for LoopAbstractionOutput<'tcx> {
    fn to_pcg_node(self, _ctxt: Ctxt) -> PcgNode<'tcx> {
        self.0.into()
    }
}

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
pub struct AbstractionInputTarget<'tcx>(pub(crate) PcgNode<'tcx>);

impl<'tcx, Ctxt> PcgNodeLike<'tcx, Ctxt> for AbstractionInputTarget<'tcx> {
    fn to_pcg_node(self, _ctxt: Ctxt) -> PcgNode<'tcx> {
        self.0
    }
}

impl<'a, 'tcx> HasValidityCheck<CompilerCtxt<'a, 'tcx>> for AbstractionInputTarget<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.0.check_validity(ctxt)
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref)]
pub struct AbstractionOutputTarget<'tcx>(pub(crate) LocalNode<'tcx>);

impl<'tcx, Ctxt> LabelPlace<'tcx, Ctxt> for AbstractionOutputTarget<'tcx> {
    fn label_place(&mut self, labeller: &impl PlaceLabeller<'tcx, Ctxt>, ctxt: Ctxt) -> bool {
        self.0.label_place(labeller, ctxt)
    }
}

impl<'tcx> LabelLifetimeProjection<'tcx> for AbstractionOutputTarget<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        label: Option<LifetimeProjectionLabel>,
    ) -> LabelLifetimeProjectionResult {
        self.0.label_lifetime_projection(label)
    }
}

impl<'a, 'tcx> HasValidityCheck<CompilerCtxt<'a, 'tcx>> for AbstractionOutputTarget<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> Result<(), String> {
        self.0.check_validity(ctxt)
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for AbstractionOutputTarget<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        self.0.display_output(ctxt, mode)
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref)]
pub struct FunctionCallAbstractionOutput<'tcx>(pub(crate) LocalLifetimeProjection<'tcx>);

impl<'tcx> From<LifetimeProjection<'tcx, Place<'tcx>>> for FunctionCallAbstractionOutput<'tcx> {
    fn from(value: LifetimeProjection<'tcx, Place<'tcx>>) -> Self {
        FunctionCallAbstractionOutput(value.into())
    }
}

impl<'tcx, Ctxt> DisplayWithCtxt<Ctxt> for FunctionCallAbstractionOutput<'tcx>
where
    LocalLifetimeProjection<'tcx>: DisplayWithCtxt<Ctxt>,
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        self.0.display_output(ctxt, mode)
    }
}

impl<'tcx, Ctxt> PcgNodeLike<'tcx, Ctxt> for FunctionCallAbstractionOutput<'tcx> {
    fn to_pcg_node(self, _ctxt: Ctxt) -> PcgNode<'tcx> {
        self.0.into()
    }
}

impl<'a, 'tcx> HasValidityCheck<CompilerCtxt<'a, 'tcx>> for FunctionCallAbstractionOutput<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> Result<(), String> {
        self.0.check_validity(ctxt)
    }
}

impl<'tcx> LabelLifetimeProjection<'tcx> for FunctionCallAbstractionOutput<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        label: Option<LifetimeProjectionLabel>,
    ) -> LabelLifetimeProjectionResult {
        self.0.label_lifetime_projection(label)
    }
}

impl<'tcx> PcgLifetimeProjectionLike<'tcx> for FunctionCallAbstractionOutput<'tcx> {
    fn to_pcg_lifetime_projection(self) -> LifetimeProjection<'tcx> {
        self.0.to_pcg_lifetime_projection()
    }
}

impl<'tcx, Ctxt> LabelPlace<'tcx, Ctxt> for FunctionCallAbstractionOutput<'tcx> {
    fn label_place(&mut self, labeller: &impl PlaceLabeller<'tcx, Ctxt>, ctxt: Ctxt) -> bool {
        self.0.label_place(labeller, ctxt)
    }
}
