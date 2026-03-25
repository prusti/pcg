use std::{borrow::Cow, marker::PhantomData};

use derive_more::{Deref, DerefMut};

use crate::{
    borrow_pcg::{
        FunctionData,
        abstraction::{
            CheckOutlivesError, FunctionShape, FunctionShapeDataSource, MakeFunctionShapeError,
        },
        borrow_pcg_edge::{BlockedNode, LocalNode},
        domain::{FunctionCallAbstractionInput, FunctionCallAbstractionOutput},
        edge::abstraction::AbstractionBlockEdge,
        edge_data::{
            EdgeData, LabelEdgeLifetimeProjections, LabelEdgePlaces, LabelNodePredicate,
            NodeReplacement,
        },
        has_pcs_elem::{LabelLifetimeProjectionResult, PlaceLabeller},
        region_projection::{LifetimeProjectionLabel, PcgRegion},
    },
    coupling::CoupledEdgeKind,
    pcg::PcgNodeWithPlace,
    rustc_interface::{
        hir::def_id::DefId,
        infer::infer::TyCtxtInferExt,
        middle::{
            mir::Location,
            ty::{self, GenericArgsRef},
        },
        span::{Span, def_id::LocalDefId},
        trait_selection::infer::outlives::env::OutlivesEnvironment,
    },
    utils::{
        CompilerCtxt, DebugCtxt, HasBorrowCheckerCtxt, PcgPlace, Place,
        data_structures::HashSet,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        validity::{HasValidityCheck, has_validity_check_node_wrapper},
    },
};

use crate::coupling::HyperEdge;

#[derive(Clone)]
pub struct DefinedFnSigShapeDataSource<'tcx> {
    def_id: DefId,
    outlives: OutlivesEnvironment<'tcx>,
}

impl<'tcx> DefinedFnSigShapeDataSource<'tcx> {
    /// Returns the function signature with late-bound regions liberated.
    fn sig(&self, tcx: ty::TyCtxt<'tcx>) -> ty::FnSig<'tcx> {
        let fn_sig = tcx.fn_sig(self.def_id).instantiate_identity();
        tcx.liberate_late_bound_regions(self.def_id, fn_sig)
    }
}

impl<'tcx> FunctionShapeDataSource<'tcx> for DefinedFnSigShapeDataSource<'tcx> {
    type Ctxt = ty::TyCtxt<'tcx>;

    fn input_tys(&self, ctxt: Self::Ctxt) -> Vec<ty::Ty<'tcx>> {
        self.sig(ctxt).inputs().to_vec()
    }

    fn output_ty(&self, ctxt: Self::Ctxt) -> ty::Ty<'tcx> {
        self.sig(ctxt).output()
    }

    fn outlives(
        &self,
        sup: PcgRegion<'tcx>,
        sub: PcgRegion<'tcx>,
        ctxt: Self::Ctxt,
    ) -> Result<bool, CheckOutlivesError<'tcx>> {
        if sup.is_static() || sup == sub {
            return Ok(true);
        }
        match (sup, sub) {
            (PcgRegion::RegionVid(_), PcgRegion::RegionVid(_) | PcgRegion::ReStatic) => {
                Err(CheckOutlivesError::CannotCompareRegions { sup, sub })
            }
            (PcgRegion::ReLateParam(_), PcgRegion::RegionVid(_)) => Ok(false),
            (PcgRegion::RegionVid(_), PcgRegion::ReLateParam(_)) => Ok(true),
            _ => Ok(self.outlives.free_region_map().sub_free_regions(
                ctxt,
                sub.rust_region(ctxt),
                sup.rust_region(ctxt),
            )),
        }
    }
}

impl<'tcx> DefinedFnSigShapeDataSource<'tcx> {
    #[rustversion::before(2025-05-24)]
    pub(crate) fn new(
        _def_id: DefId,
        _tcx: ty::TyCtxt<'tcx>,
    ) -> Result<Self, MakeFunctionShapeError<'tcx>> {
        Err(MakeFunctionShapeError::UnsupportedRustVersion)
    }

    #[rustversion::since(2025-05-24)]
    #[allow(clippy::unnecessary_wraps)]
    pub(crate) fn new(
        def_id: DefId,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Result<Self, MakeFunctionShapeError<'tcx>> {
        let typing_env = ty::TypingEnv::post_analysis(tcx, def_id);
        let (_, param_env) = tcx.infer_ctxt().build_with_typing_env(typing_env);
        let outlives = OutlivesEnvironment::from_normalized_bounds(
            param_env,
            vec![],
            vec![],
            HashSet::default(),
        );
        Ok(Self { def_id, outlives })
    }
}

pub(crate) struct FnCallDataSource<'a, 'tcx> {
    input_tys: Vec<ty::Ty<'tcx>>,
    output_ty: ty::Ty<'tcx>,
    location: Location,
    _marker: PhantomData<&'a ()>,
}

impl<'a, 'tcx: 'a> FnCallDataSource<'a, 'tcx> {
    pub(crate) fn new(
        location: Location,
        input_tys: Vec<ty::Ty<'tcx>>,
        output_ty: ty::Ty<'tcx>,
    ) -> Self {
        Self {
            location,
            input_tys,
            output_ty,
            _marker: PhantomData,
        }
    }
}

impl<'a, 'tcx: 'a> FunctionShapeDataSource<'tcx> for FnCallDataSource<'a, 'tcx> {
    type Ctxt = CompilerCtxt<'a, 'tcx>;
    fn input_tys(&self, _ctxt: CompilerCtxt<'a, 'tcx>) -> Vec<ty::Ty<'tcx>> {
        self.input_tys.clone()
    }
    fn output_ty(&self, _ctxt: CompilerCtxt<'a, 'tcx>) -> ty::Ty<'tcx> {
        self.output_ty
    }
    fn outlives(
        &self,
        sup: PcgRegion<'tcx>,
        sub: PcgRegion<'tcx>,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> Result<bool, CheckOutlivesError<'tcx>> {
        Ok(ctxt.borrow_checker.outlives(sup, sub, self.location))
    }
}

pub(crate) struct DefinedFnCallShapeDataSource<'a, 'tcx> {
    call: DefinedFnCall<'tcx>,
    outlives: OutlivesEnvironment<'tcx>,
    _marker: PhantomData<&'a ()>,
}

impl<'a, 'tcx: 'a> DefinedFnCallShapeDataSource<'a, 'tcx> {
    #[rustversion::before(2025-05-24)]
    pub(crate) fn new(
        _call: DefinedFnCall<'tcx>,
        _tcx: ty::TyCtxt<'tcx>,
    ) -> Result<Self, MakeFunctionShapeError<'tcx>> {
        Err(MakeFunctionShapeError::UnsupportedRustVersion)
    }

    #[rustversion::since(2025-05-24)]
    #[allow(clippy::unnecessary_wraps)]
    pub(crate) fn new(
        call: DefinedFnCall<'tcx>,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Result<Self, MakeFunctionShapeError<'tcx>> {
        let typing_env = ty::TypingEnv::post_analysis(tcx, call.function_data.def_id);
        let (_, param_env) = tcx.infer_ctxt().build_with_typing_env(typing_env);
        let outlives = OutlivesEnvironment::from_normalized_bounds(
            param_env,
            vec![],
            vec![],
            HashSet::default(),
        );
        Ok(Self {
            call,
            outlives,
            _marker: PhantomData,
        })
    }
}

impl<'tcx> FunctionData<'tcx> {
    #[must_use]
    pub fn identity_fn_sig(self, tcx: ty::TyCtxt<'tcx>) -> ty::FnSig<'tcx> {
        let fn_sig = tcx.fn_sig(self.def_id).instantiate_identity();
        tcx.liberate_late_bound_regions(self.def_id, fn_sig)
    }

    /// Returns the function signature instantiated with the given substs.
    #[must_use]
    pub fn fn_sig(self, tcx: ty::TyCtxt<'tcx>, substs: GenericArgsRef<'tcx>) -> ty::FnSig<'tcx> {
        let fn_sig = tcx.fn_sig(self.def_id).instantiate(tcx, substs);
        tcx.liberate_late_bound_regions(self.def_id, fn_sig)
    }
}

impl<'a, 'tcx: 'a> DefinedFnCallShapeDataSource<'a, 'tcx> {
    /// Maps an instantiated region back to the corresponding identity region
    /// for outlives checking against the function's param_env. Returns `None`
    /// if the region cannot be mapped (e.g. nested inside a type argument).
    fn region_for_outlives_check(
        &self,
        region: PcgRegion<'tcx>,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Option<PcgRegion<'tcx>> {
        if let Some(index) = self
            .call
            .caller_substs
            .regions()
            .position(|r| PcgRegion::from(r) == region)
        {
            let fn_ty = tcx
                .type_of(self.call.function_data.def_id)
                .instantiate_identity();
            let ty::TyKind::FnDef(_def_id, identity_substs) = fn_ty.kind() else {
                panic!("Expected a function type");
            };
            Some(identity_substs.region_at(index).into())
        } else {
            None
        }
    }
}

impl<'a, 'tcx: 'a> FunctionShapeDataSource<'tcx> for DefinedFnCallShapeDataSource<'a, 'tcx> {
    type Ctxt = CompilerCtxt<'a, 'tcx>;
    fn input_tys(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> Vec<ty::Ty<'tcx>> {
        self.call
            .function_data
            .fn_sig(ctxt.tcx(), self.call.caller_substs)
            .inputs()
            .to_vec()
    }
    fn output_ty(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> ty::Ty<'tcx> {
        self.call
            .function_data
            .fn_sig(ctxt.tcx(), self.call.caller_substs)
            .output()
    }

    fn outlives(
        &self,
        sup: PcgRegion<'tcx>,
        sub: PcgRegion<'tcx>,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> Result<bool, CheckOutlivesError<'tcx>> {
        if sup.is_static() || sup == sub {
            return Ok(true);
        }
        // Map instantiated regions back to identity regions for the param_env
        // check. If a region can't be mapped (e.g. nested in a type arg or
        // late-bound), conservatively return false.
        let Some(sup) = self.region_for_outlives_check(sup, ctxt.tcx()) else {
            return Ok(false);
        };
        let Some(sub) = self.region_for_outlives_check(sub, ctxt.tcx()) else {
            return Ok(false);
        };
        let result = match (sup, sub) {
            (PcgRegion::RegionVid(_), PcgRegion::RegionVid(_) | PcgRegion::ReStatic) => {
                Err(CheckOutlivesError::CannotCompareRegions { sup, sub })
            }
            (PcgRegion::ReLateParam(_), PcgRegion::RegionVid(_)) => Ok(false),
            (PcgRegion::RegionVid(_), PcgRegion::ReLateParam(_)) => Ok(true),
            _ => Ok(self.outlives.free_region_map().sub_free_regions(
                ctxt.tcx(),
                sub.rust_region(ctxt.tcx()),
                sup.rust_region(ctxt.tcx()),
            )),
        }?;
        Ok(result)
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct FunctionCallData<'tcx> {
    pub(crate) call: DefinedFnCall<'tcx>,
    pub(crate) caller_def_id: LocalDefId,
    pub(crate) operand_tys: Vec<ty::Ty<'tcx>>,
    pub(crate) span: Span,
}

impl<'tcx> FunctionCallData<'tcx> {
    pub(crate) fn new(
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        operand_tys: Vec<ty::Ty<'tcx>>,
        caller_def_id: LocalDefId,
        span: Span,
    ) -> Self {
        Self {
            call: DefinedFnCall::new(FunctionData::new(def_id), substs),
            caller_def_id,
            operand_tys,
            span,
        }
    }

    pub(crate) fn shape(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<FunctionShape, MakeFunctionShapeError<'tcx>> {
        let data = DefinedFnCallShapeDataSource::new(self.call, ctxt.tcx)?;
        FunctionShape::new(&data, ctxt).map_err(MakeFunctionShapeError::CheckOutlivesError)
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
pub(crate) struct DefinedFnCall<'tcx> {
    pub(crate) function_data: FunctionData<'tcx>,
    pub(crate) caller_substs: GenericArgsRef<'tcx>,
}

impl<'tcx> DefinedFnCall<'tcx> {
    pub(crate) fn new(
        function_data: FunctionData<'tcx>,
        caller_substs: GenericArgsRef<'tcx>,
    ) -> Self {
        Self {
            function_data,
            caller_substs,
        }
    }

}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub struct FunctionCallAbstractionEdgeMetadata<'tcx> {
    pub(crate) location: Location,
    pub(crate) defined_fn_call: Option<DefinedFnCall<'tcx>>,
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for FunctionCallAbstractionEdgeMetadata<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(
            format!(
                "call{} at {:?}",
                if let Some(defined_fn_call) = &self.defined_fn_call {
                    format!(
                        " {}",
                        ctxt.tcx()
                            .def_path_str(defined_fn_call.function_data.def_id)
                    )
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
        self.defined_fn_call
            .as_ref()
            .map(|f| f.function_data.def_id)
    }

    pub fn function_data(&self) -> Option<FunctionData<'tcx>> {
        self.defined_fn_call.as_ref().map(|f| f.function_data)
    }

    pub fn shape(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<FunctionShape, MakeFunctionShapeError<'tcx>> {
        let Some(call) = self.defined_fn_call.as_ref() else {
            return Err(MakeFunctionShapeError::NoFunctionData);
        };
        let data = DefinedFnCallShapeDataSource::new(*call, ctxt.tcx)?;
        FunctionShape::new(&data, ctxt).map_err(MakeFunctionShapeError::CheckOutlivesError)
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
        self.metadata.function_data().as_ref().map(|f| f.def_id)
    }
    pub fn substs(&self) -> Option<GenericArgsRef<'tcx>> {
        self.metadata
            .defined_fn_call
            .as_ref()
            .map(|f| f.caller_substs)
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
