use derive_more::{Deref, DerefMut, From};

use super::region_projection::LifetimeProjection;
use crate::{
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        edge_data::LabelPlacePredicate,
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionPredicate,
            LabelLifetimeProjectionResult, LabelNodeContext, LabelPlace, LabelPlaceWithContext,
            PlaceLabeller,
        },
        region_projection::{
            LifetimeProjectionLabel, LocalLifetimeProjection, PcgLifetimeProjectionBaseLike,
            PcgLifetimeProjectionLike, PlaceOrConst,
        },
    },
    pcg::{PcgNode, PcgNodeLike},
    utils::{
        CompilerCtxt, HasBorrowCheckerCtxt, Place, display::{DisplayOutput, DisplayWithCtxt},
        maybe_remote::MaybeRemotePlace, place::maybe_old::MaybeLabelledPlace,
        validity::HasValidityCheck,
    },
};

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref, DerefMut)]
pub struct FunctionCallAbstractionInput<'tcx>(
    pub(crate) LifetimeProjection<'tcx, PlaceOrConst<'tcx, MaybeLabelledPlace<'tcx>>>,
);

impl<'tcx> LifetimeProjection<'tcx, PlaceOrConst<'tcx, MaybeLabelledPlace<'tcx>>> {
    pub fn try_to_local_lifetime_projection(self) -> Option<LocalLifetimeProjection<'tcx>> {
        match self.base {
            PlaceOrConst::Place(maybe_labelled_place) => Some(self.with_base(maybe_labelled_place)),
            PlaceOrConst::Const(_) => None,
        }
    }
}

impl<'a, 'tcx> LabelLifetimeProjection<'a, 'tcx>
    for PcgNode<'tcx, MaybeLabelledPlace<'tcx>, PlaceOrConst<'tcx, MaybeLabelledPlace<'tcx>>>
{
    fn label_lifetime_projection(
        &mut self,
        predicate: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        match self {
            PcgNode::LifetimeProjection(rp) => rp.label_lifetime_projection(predicate, label, ctxt),
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

impl<'a, 'tcx> LabelLifetimeProjection<'a, 'tcx> for FunctionCallAbstractionInput<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        predicate: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        self.0.label_lifetime_projection(predicate, label, ctxt)
    }
}

impl<'tcx> PcgNodeLike<'tcx> for FunctionCallAbstractionInput<'tcx> {
    fn to_pcg_node<C: Copy>(self, ctxt: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx> {
        self.0.to_pcg_node(ctxt)
    }
}

impl<'tcx> HasValidityCheck<'_, 'tcx> for FunctionCallAbstractionInput<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.0.check_validity(ctxt)
    }
}

impl<'tcx, Ctxt> DisplayWithCtxt<Ctxt> for FunctionCallAbstractionInput<'tcx>
where
    LifetimeProjection<'tcx, PlaceOrConst<'tcx, MaybeLabelledPlace<'tcx>>>: DisplayWithCtxt<Ctxt>,
{
    fn output(&self, ctxt: Ctxt) -> DisplayOutput {
        self.0.output(ctxt)
    }
}

impl<'tcx> LabelPlaceWithContext<'tcx, LabelNodeContext> for FunctionCallAbstractionInput<'tcx> {
    fn label_place_with_context(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        label_context: LabelNodeContext,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.0
            .label_place_with_context(predicate, labeller, label_context, ctxt)
    }
}

impl<'tcx> LabelPlaceWithContext<'tcx, LabelNodeContext>
    for LifetimeProjection<'tcx, PlaceOrConst<'tcx, MaybeLabelledPlace<'tcx>>>
{
    fn label_place_with_context(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        label_context: LabelNodeContext,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.base
            .label_place_with_context(predicate, labeller, label_context, ctxt)
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref)]
pub struct LoopAbstractionInput<'tcx>(pub(crate) PcgNode<'tcx>);

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref)]
pub struct LoopAbstractionOutput<'tcx>(pub(crate) LocalNode<'tcx>);

impl<'tcx> From<MaybeRemotePlace<'tcx>> for LoopAbstractionInput<'tcx> {
    fn from(value: MaybeRemotePlace<'tcx>) -> Self {
        LoopAbstractionInput(value.into())
    }
}

impl<'tcx> LoopAbstractionOutput<'tcx> {
    pub(crate) fn to_abstraction_output(self) -> AbstractionOutputTarget<'tcx> {
        AbstractionOutputTarget(self.0)
    }
}

impl<'a, 'tcx> LabelLifetimeProjection<'a, 'tcx> for LoopAbstractionInput<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        projection: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        self.0.label_lifetime_projection(projection, label, ctxt)
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for LoopAbstractionInput<'tcx>
{
    fn output(&self, ctxt: Ctxt) -> crate::utils::display::DisplayOutput {
        self.0.output(ctxt)
    }
}

impl<'tcx> PcgNodeLike<'tcx> for LoopAbstractionInput<'tcx> {
    fn to_pcg_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx> {
        self.0
    }
}

impl<'tcx> HasValidityCheck<'_, 'tcx> for LoopAbstractionInput<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.0.check_validity(ctxt)
    }
}

impl<'tcx> LabelPlaceWithContext<'tcx, LabelNodeContext> for LoopAbstractionInput<'tcx> {
    fn label_place_with_context(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        label_context: LabelNodeContext,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.0
            .label_place_with_context(predicate, labeller, label_context, ctxt)
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

impl<'a, 'tcx> LabelLifetimeProjection<'a, 'tcx> for LoopAbstractionOutput<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        projection: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        self.0.label_lifetime_projection(projection, label, ctxt)
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for LoopAbstractionOutput<'tcx>
{
    fn output(&self, ctxt: Ctxt) -> crate::utils::display::DisplayOutput {
        self.0.output(ctxt)
    }
}

impl<'tcx> PcgNodeLike<'tcx> for LoopAbstractionOutput<'tcx> {
    fn to_pcg_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx> {
        self.0.into()
    }
}

impl<'tcx> HasValidityCheck<'_, 'tcx> for LoopAbstractionOutput<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.0.check_validity(ctxt)
    }
}

impl<'tcx> LabelPlaceWithContext<'tcx, LabelNodeContext> for LoopAbstractionOutput<'tcx> {
    fn label_place_with_context(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        label_context: LabelNodeContext,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.0
            .label_place_with_context(predicate, labeller, label_context, ctxt)
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

impl<'tcx> PcgNodeLike<'tcx> for AbstractionInputTarget<'tcx> {
    fn to_pcg_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx> {
        self.0
    }
}

impl<'tcx> HasValidityCheck<'_, 'tcx> for AbstractionInputTarget<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.0.check_validity(ctxt)
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref)]
pub struct AbstractionOutputTarget<'tcx>(pub(crate) LocalNode<'tcx>);

impl<'tcx> LabelPlace<'tcx> for AbstractionOutputTarget<'tcx> {
    fn label_place(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.0
            .label_place_with_context(predicate, labeller, LabelNodeContext::Other, ctxt)
    }
}

impl<'a, 'tcx> LabelLifetimeProjection<'a, 'tcx> for AbstractionOutputTarget<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        projection: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        self.0.label_lifetime_projection(projection, label, ctxt)
    }
}

impl<'tcx> HasValidityCheck<'_, 'tcx> for AbstractionOutputTarget<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.0.check_validity(ctxt)
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for AbstractionOutputTarget<'tcx>
{
    fn display_string(&self, ctxt: Ctxt) -> String {
        self.0.display_string(ctxt)
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
    fn output(&self, ctxt: Ctxt) -> DisplayOutput {
        self.0.output(ctxt)
    }
}

impl<'tcx> PcgNodeLike<'tcx> for FunctionCallAbstractionOutput<'tcx> {
    fn to_pcg_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx> {
        self.0.into()
    }
}

impl<'tcx> HasValidityCheck<'_, 'tcx> for FunctionCallAbstractionOutput<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.0.check_validity(ctxt)
    }
}

impl<'a, 'tcx> LabelLifetimeProjection<'a, 'tcx> for FunctionCallAbstractionOutput<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        projection: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        self.0.label_lifetime_projection(projection, label, ctxt)
    }
}

impl<'tcx> PcgLifetimeProjectionLike<'tcx> for FunctionCallAbstractionOutput<'tcx> {
    fn to_pcg_lifetime_projection(self) -> LifetimeProjection<'tcx> {
        self.0.to_pcg_lifetime_projection()
    }
}

impl<'tcx> LabelPlaceWithContext<'tcx, LabelNodeContext> for FunctionCallAbstractionOutput<'tcx> {
    fn label_place_with_context(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        label_context: LabelNodeContext,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.0
            .label_place_with_context(predicate, labeller, label_context, ctxt)
    }
}
