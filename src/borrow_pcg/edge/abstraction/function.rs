use std::{borrow::Cow, collections::HashMap, marker::PhantomData};

use derive_more::{Deref, DerefMut};

use crate::{
    borrow_pcg::{
        FunctionData,
        abstraction::{
            ArgIdx, ArgIdxOrResult, CallShapeDataSource, CheckOutlivesError, FnShapeDataSource,
            ForCall, ForFn, FunctionShape, FunctionShapeDataSource, MakeFunctionShapeError,
        },
        borrow_pcg_edge::{BlockedNode, LocalNode},
        domain::{FunctionCallAbstractionInput, FunctionCallAbstractionOutput},
        edge::abstraction::AbstractionBlockEdge,
        edge_data::{
            EdgeData, LabelEdgeLifetimeProjections, LabelEdgePlaces, LabelNodePredicate,
            NodeReplacement,
        },
        has_pcs_elem::{LabelLifetimeProjectionResult, PlaceLabeller},
        region_projection::{LifetimeProjection, LifetimeProjectionLabel, PcgRegion},
        visitor::extract_regions,
    },
    coupling::CoupledEdgeKind,
    pcg::PcgNodeWithPlace,
    rustc_interface::{
        hir::def_id::DefId,
        middle::{
            mir::{Location, Operand},
            ty::{self, GenericArgsRef, TypeFoldable, TypeVisitableExt},
        },
        span::{Span, def_id::LocalDefId},
        trait_selection::infer::outlives::env::OutlivesEnvironment,
    },
    utils::{
        CompilerCtxt, DebugCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, HasTyCtxt, PcgPlace, Place,
        data_structures::HashSet,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        validity::{HasValidityCheck, has_validity_check_node_wrapper},
    },
};

use crate::coupling::HyperEdge;

pub(crate) struct FunctionDefShapeDataSource<'tcx> {
    fn_def_id: DefId,
    outlives: OutlivesEnvironment<'tcx>,
}
impl<'tcx, Ctxt: HasTyCtxt<'tcx> + Copy, DS: CallShapeDataSource<'tcx, Ctxt>>
    FunctionShapeDataSource<'tcx, ForCall, Ctxt> for DS
{
    fn shape_input_tys(&self, ctxt: Ctxt) -> Vec<ty::Ty<'tcx>> {
        self.call_input_tys(ctxt)
    }

    fn shape_output_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx> {
        self.call_output_ty(ctxt)
    }

    fn region_outlives(
        &self,
        sup: ty::RegionVid,
        sub: ty::RegionVid,
        ctxt: Ctxt,
    ) -> Result<bool, CheckOutlivesError<'tcx>> {
        self.call_region_outlives(sup.into(), sub, ctxt)
    }
}

impl<'tcx, Ctxt: HasTyCtxt<'tcx> + Copy> FunctionShapeDataSource<'tcx, ForFn, Ctxt>
    for FunctionDefShapeDataSource<'tcx>
{
    fn shape_input_tys(&self, ctxt: Ctxt) -> Vec<ty::Ty<'tcx>> {
        self.fn_sig(ctxt).inputs().iter().copied().collect()
    }

    fn shape_output_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx> {
        self.fn_sig(ctxt).output()
    }

    fn region_outlives(
        &self,
        sup: PcgRegion<'tcx>,
        sub: PcgRegion<'tcx>,
        ctxt: Ctxt,
    ) -> Result<bool, CheckOutlivesError<'tcx>> {
        self.fn_region_outlives(sup, sub, ctxt)
    }
}

impl<'tcx> FunctionDefShapeDataSource<'tcx> {
    pub(crate) fn new(fn_def_id: DefId, tcx: ty::TyCtxt<'tcx>) -> Self {
        let outlives = OutlivesEnvironment::from_normalized_bounds(
            tcx.param_env(fn_def_id),
            vec![],
            vec![],
            HashSet::default(),
        );
        Self {
            fn_def_id,
            outlives,
        }
    }
    pub(crate) fn fn_sig(&self, ctxt: impl HasTyCtxt<'tcx>) -> ty::FnSig<'tcx> {
        let tcx = ctxt.tcx();
        let sig = tcx.fn_sig(self.fn_def_id).instantiate_identity();
        tcx.liberate_late_bound_regions(self.fn_def_id, sig)
    }
}

impl<'tcx, Ctxt: HasTyCtxt<'tcx> + Copy> FnShapeDataSource<'tcx, Ctxt>
    for FunctionDefShapeDataSource<'tcx>
{
    fn fn_sig(&self, ctxt: Ctxt) -> ty::FnSig<'tcx> {
        self.fn_sig(ctxt.tcx())
    }

    fn fn_region_outlives(
        &self,
        sup: PcgRegion<'tcx>,
        sub: PcgRegion<'tcx>,
        ctxt: Ctxt,
    ) -> Result<bool, CheckOutlivesError<'tcx>> {
        if sup.is_static() || sup == sub {
            return Ok(true);
        }
        Ok(self.outlives.free_region_map().sub_free_regions(
            ctxt.tcx(),
            sub.rust_region(ctxt.tcx()),
            sup.rust_region(ctxt.tcx()),
        ))
    }
}

pub(crate) struct UndefinedFnCallShapeDataSource<'operands, 'tcx: 'operands> {
    pub(crate) call: FunctionCallData<'tcx, RustCallDatatypes<'operands>>,
}

impl<'operands, 'a, 'tcx: 'a + 'operands, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx> + Copy>
    CallShapeDataSource<'tcx, Ctxt> for UndefinedFnCallShapeDataSource<'operands, 'tcx>
{
    fn call_input_tys(&self, ctxt: Ctxt) -> Vec<ty::Ty<'tcx>> {
        self.call
            .inputs
            .iter()
            .map(|input| input.ty(ctxt.body(), ctxt.tcx()))
            .collect()
    }
    fn call_output_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx> {
        self.call.output_place.ty(ctxt).ty
    }

    fn call_region_outlives(
        &self,
        sup: ty::RegionVid,
        sub: ty::RegionVid,
        ctxt: Ctxt,
    ) -> Result<bool, CheckOutlivesError<'tcx>> {
        Ok(ctxt
            .bc()
            .outlives(sup.into(), sub.into(), self.call.location))
    }

    fn location(&self) -> Location {
        self.call.location
    }

    fn target(&self) -> Option<DefinedFnTarget<'tcx>> {
        None
    }
}

type DefProjection<'tcx, Idx> = LifetimeProjection<'tcx, Idx, PcgRegion<'tcx>>;
type CallProjection<'tcx> = LifetimeProjection<'tcx, Place<'tcx>, ty::RegionVid>;

pub struct DefinedFnCallShapeDataSource<'operands, 'tcx: 'operands> {
    call: FunctionCallData<'tcx, DefinedFnCallDatatypes<'operands>>,
    input_def_call_map: HashMap<DefProjection<'tcx, ArgIdx>, CallProjection<'tcx>>,
    output_def_call_map: HashMap<DefProjection<'tcx, ()>, CallProjection<'tcx>>,
    outlives: OutlivesEnvironment<'tcx>,
}

impl<'operands, 'tcx: 'operands> DefinedFnCallShapeDataSource<'operands, 'tcx> {
    #[rustversion::since(2025-05-24)]
    pub(crate) fn new(
        call: DefinedFnCallData<'operands, 'tcx>,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Result<Self, MakeFunctionShapeError<'tcx>> {
        let sig = call.identity_fn_sig(tcx);
        todo!()
    }

    pub(crate) fn lookup_region_in_sig(
        &self,
        region: ty::RegionVid,
    ) -> PcgRegion<'tcx> {
        todo!()
    }
}

impl<'tcx> FunctionData<'tcx> {
    #[must_use]
    pub fn identity_fn_sig(self, tcx: ty::TyCtxt<'tcx>) -> ty::FnSig<'tcx> {
        self.fn_sig(None, tcx)
    }

    #[must_use]
    pub(crate) fn fn_sig(
        self,
        substs: Option<GenericArgsRef<'tcx>>,
        tcx: ty::TyCtxt<'tcx>,
    ) -> ty::FnSig<'tcx> {
        let fn_sig = match substs {
            Some(substs) => tcx.fn_sig(self.def_id).instantiate(tcx, substs),
            None => tcx.fn_sig(self.def_id).instantiate_identity(),
        };
        tcx.liberate_late_bound_regions(self.def_id, fn_sig)
    }
}

impl<'operands, 'a, 'tcx: 'a + 'operands, Ctxt: HasCompilerCtxt<'a, 'tcx> + Copy>
    CallShapeDataSource<'tcx, Ctxt> for DefinedFnCallShapeDataSource<'operands, 'tcx>
{
    fn call_input_tys(&self, ctxt: Ctxt) -> Vec<ty::Ty<'tcx>> {
        self.call
            .inputs
            .iter()
            .map(|input| input.ty(ctxt.body(), ctxt.tcx()))
            .collect()
    }
    fn call_output_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx> {
        self.call.output_place.ty(ctxt).ty
    }

    fn call_region_outlives(
        &self,
        sup: ty::RegionVid,
        sub: ty::RegionVid,
        ctxt: Ctxt,
    ) -> Result<bool, CheckOutlivesError<'tcx>> {
        let sup = self.lookup_region_in_sig(sup);
        let sub = self.lookup_region_in_sig(sub);
        Ok(self.outlives.free_region_map().sub_free_regions(
            ctxt.tcx(),
            sub.rust_region(ctxt.tcx()),
            sup.rust_region(ctxt.tcx()),
        ))
    }

    fn location(&self) -> Location {
        self.call.location
    }

    fn target(&self) -> Option<DefinedFnTarget<'tcx>> {
        Some(self.call.target)
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub(crate) struct RustCallDatatypes<'operands>(PhantomData<&'operands ()>);

impl<'operands, 'tcx: 'operands> CallDatatypes<'tcx> for RustCallDatatypes<'operands> {
    type Inputs = &'operands [&'operands Operand<'tcx>];
}

#[derive(Clone, Copy)]
pub(crate) struct DefinedFnCallDatatypes<'operands>(PhantomData<&'operands ()>);

impl<'operands, 'tcx: 'operands> CallDatatypes<'tcx> for DefinedFnCallDatatypes<'operands> {
    type Target = DefinedFnTarget<'tcx>;
    type Inputs = &'operands [&'operands Operand<'tcx>];
}

pub trait CallDatatypes<'tcx> {
    type Target = Option<DefinedFnTarget<'tcx>>;
    type CallerDefId: PartialEq + Eq + Clone + std::fmt::Debug + std::hash::Hash = LocalDefId;
    type Inputs;
    type OutputPlace: PartialEq + Eq + Clone + std::fmt::Debug + std::hash::Hash = Place<'tcx>;
    type Location: PartialEq + Eq + Clone + std::fmt::Debug + std::hash::Hash = Location;
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub struct DefinedFnTarget<'tcx> {
    pub(crate) fn_def_id: DefId,
    pub(crate) substs: GenericArgsRef<'tcx>,
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub struct FunctionCallData<'tcx, D: CallDatatypes<'tcx>> {
    pub(crate) target: D::Target,
    pub(crate) caller_def_id: D::CallerDefId,
    pub(crate) span: Span,
    pub(crate) inputs: D::Inputs,
    pub(crate) output_place: D::OutputPlace,
    pub(crate) location: D::Location,
}

pub(crate) type DefinedFnCallData<'operands, 'tcx: 'operands> =
    FunctionCallData<'tcx, DefinedFnCallDatatypes<'operands>>;

impl<'operands, 'tcx: 'operands> FunctionCallData<'tcx, RustCallDatatypes<'operands>> {
    pub(crate) fn as_defined_fn_call_data(
        self,
    ) -> Option<FunctionCallData<'tcx, DefinedFnCallDatatypes<'operands>>> {
        self.target.map(|target| FunctionCallData {
            target,
            caller_def_id: self.caller_def_id,
            span: self.span,
            inputs: self.inputs,
            output_place: self.output_place,
            location: self.location,
        })
    }
}

impl<'operands, 'tcx: 'operands> DefinedFnCallData<'operands, 'tcx> {
    pub(crate) fn fn_sig(self, tcx: ty::TyCtxt<'tcx>) -> ty::FnSig<'tcx> {
        let instantiated = tcx
            .fn_sig(self.target.fn_def_id)
            .instantiate(tcx, self.target.substs);
        tcx.liberate_late_bound_regions(self.target.fn_def_id, instantiated)
    }

    pub(crate) fn identity_fn_sig(self, tcx: ty::TyCtxt<'tcx>) -> ty::FnSig<'tcx> {
        let instantiated = tcx.fn_sig(self.target.fn_def_id).instantiate_identity();
        tcx.liberate_late_bound_regions(self.target.fn_def_id, instantiated)
    }
}

pub(crate) type FunctionCallAbstractionEdge<'tcx, P = Place<'tcx>> = AbstractionBlockEdge<
    'tcx,
    FunctionCallAbstractionInput<'tcx, P>,
    FunctionCallAbstractionOutput<'tcx>,
>;

impl<'tcx> FunctionCallAbstractionEdge<'tcx> {
    #[must_use]
    pub fn to_hyper_edge(
        &self,
    ) -> HyperEdge<FunctionCallAbstractionInput<'tcx>, FunctionCallAbstractionOutput<'tcx>> {
        HyperEdge::new(vec![self.input], vec![self.output])
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Deref, DerefMut)]
pub struct AbstractionBlockEdgeWithMetadata<Metadata, Edge> {
    pub(crate) metadata: Metadata,
    #[deref]
    #[deref_mut]
    pub(crate) edge: Edge,
}

impl<Metadata, Input: Copy, Output: Copy>
    AbstractionBlockEdgeWithMetadata<Metadata, AbstractionBlockEdge<'_, Input, Output>>
{
    pub(crate) fn into_singleton_coupled_edge(self) -> CoupledEdgeKind<Metadata, Input, Output> {
        CoupledEdgeKind::new(self.metadata, self.edge.to_singleton_hyper_edge())
    }
}
#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub struct FunctionCallAbstractionEdgeMetadata<'tcx> {
    pub(crate) location: Location,
    pub(crate) target: Option<DefinedFnTarget<'tcx>>,
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for FunctionCallAbstractionEdgeMetadata<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(
            format!(
                "call{} at {:?}",
                if let Some(target) = &self.target {
                    format!(" {}", ctxt.tcx().def_path_str(target.fn_def_id))
                } else {
                    String::new()
                },
                self.location
            )
            .into(),
        )
    }
}
impl<'tcx> FunctionCallAbstractionEdgeMetadata<'tcx> {
    pub fn location(&self) -> Location {
        self.location
    }

    pub fn def_id(&self) -> Option<DefId> {
        self.target.as_ref().map(|f| f.fn_def_id)
    }

    pub fn function_data(&self) -> Option<FunctionData<'tcx>> {
        self.target
            .map(|target| FunctionData::new(target.fn_def_id))
    }
}

pub type FunctionCallAbstraction<'tcx, P = Place<'tcx>> = AbstractionBlockEdgeWithMetadata<
    FunctionCallAbstractionEdgeMetadata<'tcx>,
    FunctionCallAbstractionEdge<'tcx, P>,
>;

impl<'tcx, Ctxt: Copy, P: PcgPlace<'tcx, Ctxt>> LabelEdgeLifetimeProjections<'tcx, Ctxt, P>
    for FunctionCallAbstraction<'tcx, P>
where
    FunctionCallAbstractionEdge<'tcx, P>: LabelEdgeLifetimeProjections<'tcx, Ctxt, P>,
{
    fn label_lifetime_projections(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: Ctxt,
    ) -> LabelLifetimeProjectionResult {
        self.edge.label_lifetime_projections(predicate, label, ctxt)
    }
}

impl<'tcx, Ctxt: DebugCtxt + Copy, P: PcgPlace<'tcx, Ctxt>> LabelEdgePlaces<'tcx, Ctxt, P>
    for FunctionCallAbstraction<'tcx, P>
where
    FunctionCallAbstractionEdge<'tcx, P>: LabelEdgePlaces<'tcx, Ctxt, P>,
{
    fn label_blocked_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>> {
        self.edge.label_blocked_places(predicate, labeller, ctxt)
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>> {
        self.edge.label_blocked_by_places(predicate, labeller, ctxt)
    }
}

impl<'tcx, Ctxt: Copy + DebugCtxt, P: PcgPlace<'tcx, Ctxt>> EdgeData<'tcx, Ctxt, P>
    for FunctionCallAbstraction<'tcx, P>
where
    FunctionCallAbstractionEdge<'tcx, P>: EdgeData<'tcx, Ctxt, P>,
{
    fn blocks_node<'slf>(&self, node: BlockedNode<'tcx, P>, ctxt: Ctxt) -> bool {
        self.edge.blocks_node(node, ctxt)
    }

    fn blocked_nodes<'slf>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Box<dyn std::iter::Iterator<Item = PcgNodeWithPlace<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        self.edge.blocked_nodes(ctxt)
    }

    fn blocked_by_nodes<'slf>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        self.edge.blocked_by_nodes(ctxt)
    }
}

has_validity_check_node_wrapper!(FunctionCallAbstraction<'tcx, P>);

impl<Ctxt: Copy, Metadata: DisplayWithCtxt<Ctxt>, Edge: DisplayWithCtxt<Ctxt>> DisplayWithCtxt<Ctxt>
    for AbstractionBlockEdgeWithMetadata<Metadata, Edge>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Seq(vec![
            self.metadata.display_output(ctxt, mode),
            DisplayOutput::Text(Cow::Borrowed(": ")),
            self.edge.display_output(ctxt, mode),
        ])
    }
}

impl<'tcx> FunctionCallAbstraction<'tcx> {
    pub fn def_id(&self) -> Option<DefId> {
        self.metadata.target.map(|target| target.fn_def_id)
    }
    pub fn substs(&self) -> Option<GenericArgsRef<'tcx>> {
        self.metadata.target.map(|target| target.substs)
    }

    pub fn location(&self) -> Location {
        self.metadata.location
    }

    pub fn edge(
        &self,
    ) -> &AbstractionBlockEdge<
        'tcx,
        FunctionCallAbstractionInput<'tcx>,
        FunctionCallAbstractionOutput<'tcx>,
    > {
        &self.edge
    }

    pub fn new(
        metadata: FunctionCallAbstractionEdgeMetadata<'tcx>,
        edge: AbstractionBlockEdge<
            'tcx,
            FunctionCallAbstractionInput<'tcx>,
            FunctionCallAbstractionOutput<'tcx>,
        >,
    ) -> Self {
        Self { metadata, edge }
    }
}
