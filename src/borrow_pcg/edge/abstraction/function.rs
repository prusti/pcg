use std::borrow::Cow;

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
            ty::{self, GenericArgsRef, TypeVisitableExt},
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

pub struct FunctionDataShapeDataSource<'tcx> {
    input_tys: Vec<ty::Ty<'tcx>>,
    output_ty: ty::Ty<'tcx>,
    def_id: DefId,
    caller_substs: Option<GenericArgsRef<'tcx>>,
    outlives: OutlivesEnvironment<'tcx>,
}

impl<'tcx> FunctionDataShapeDataSource<'tcx> {
    #[rustversion::before(2025-05-24)]
    pub(crate) fn new(
        _data: FunctionData<'tcx>,
        _caller_substs: Option<GenericArgsRef<'tcx>>,
        _ctxt: ty::TyCtxt<'tcx>,
    ) -> Result<Self, MakeFunctionShapeError> {
        Err(MakeFunctionShapeError::UnsupportedRustVersion)
    }

    #[rustversion::since(2025-05-24)]
    pub(crate) fn new(
        data: FunctionData<'tcx>,
        caller_substs: Option<GenericArgsRef<'tcx>>,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Result<Self, MakeFunctionShapeError> {
        let sig = data.identity_fn_sig(tcx);
        let typing_env = ty::TypingEnv::post_analysis(tcx, data.def_id);
        let (_, param_env) = tcx.infer_ctxt().build_with_typing_env(typing_env);
        if sig.has_aliases() {
            return Err(MakeFunctionShapeError::ContainsAliasType);
        }
        let outlives = OutlivesEnvironment::from_normalized_bounds(
            param_env,
            vec![],
            vec![],
            Default::default(),
        );
        Ok(Self {
            def_id: data.def_id,
            input_tys: sig.inputs().to_vec(),
            output_ty: sig.output(),
            outlives,
            caller_substs,
        })
    }
}

impl<'tcx> FunctionData<'tcx> {
    pub(crate) fn identity_fn_sig(&self, tcx: ty::TyCtxt<'tcx>) -> ty::FnSig<'tcx> {
        let fn_sig = tcx.fn_sig(self.def_id).instantiate_identity();
        tcx.liberate_late_bound_regions(self.def_id, fn_sig)
    }
}

impl<'tcx> FunctionDataShapeDataSource<'tcx> {
    pub(crate) fn region_for_outlives_check(
        &self,
        region: PcgRegion,
        tcx: ty::TyCtxt<'tcx>,
    ) -> PcgRegion {
        if let Some(substs) = self.caller_substs
            && let Some(index) = substs.regions().position(|r| PcgRegion::from(r) == region)
        {
            let fn_ty = tcx.type_of(self.def_id).instantiate_identity();
            let ty::TyKind::FnDef(_def_id, identity_substs) = fn_ty.kind() else {
                panic!("Expected a function type");
            };
            identity_substs.region_at(index).into()
        } else {
            region
        }
    }
}

impl<'tcx> FunctionShapeDataSource<'tcx> for FunctionDataShapeDataSource<'tcx> {
    type Ctxt = ty::TyCtxt<'tcx>;
    fn input_tys(&self, _ctxt: ty::TyCtxt<'tcx>) -> Vec<ty::Ty<'tcx>> {
        self.input_tys.clone()
    }
    fn output_ty(&self, _ctxt: ty::TyCtxt<'tcx>) -> ty::Ty<'tcx> {
        self.output_ty
    }

    fn outlives(
        &self,
        sup: PcgRegion,
        sub: PcgRegion,
        ctxt: ty::TyCtxt<'tcx>,
    ) -> Result<bool, CheckOutlivesError> {
        if sup.is_static() || sup == sub {
            return Ok(true);
        }
        let sup = self.region_for_outlives_check(sup, ctxt);
        let sub = self.region_for_outlives_check(sub, ctxt);
        let result = match (sup, sub) {
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
        }?;
        Ok(result)
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct FunctionCallData<'tcx> {
    pub(crate) function_data: FunctionData<'tcx>,
    pub(crate) substs: GenericArgsRef<'tcx>,
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
            function_data: FunctionData::new(def_id),
            substs,
            caller_def_id,
            operand_tys,
            span,
        }
    }

    pub(crate) fn shape(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<FunctionShape, MakeFunctionShapeError> {
        let data =
            FunctionDataShapeDataSource::new(self.function_data, Some(self.substs), ctxt.tcx)?;
        FunctionShape::new(&data, ctxt.tcx).map_err(MakeFunctionShapeError::CheckOutlivesError)
    }
}

pub(crate) type FunctionCallAbstractionEdge<'tcx, P = Place<'tcx>> = AbstractionBlockEdge<
    'tcx,
    FunctionCallAbstractionInput<'tcx, P>,
    FunctionCallAbstractionOutput<'tcx>,
>;

impl<'tcx> FunctionCallAbstractionEdge<'tcx> {
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
    pub(crate) function_data: Option<FunctionData<'tcx>>,
    pub(crate) caller_substs: Option<GenericArgsRef<'tcx>>,
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for FunctionCallAbstractionEdgeMetadata<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(
            format!(
                "call{} at {:?}",
                if let Some(function_data) = &self.function_data {
                    format!(" {}", ctxt.tcx().def_path_str(function_data.def_id))
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
        self.function_data.as_ref().map(|f| f.def_id)
    }

    pub fn function_data(&self) -> Option<FunctionData<'tcx>> {
        self.function_data
    }

    pub fn shape(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<FunctionShape, MakeFunctionShapeError> {
        let function_data = self
            .function_data
            .as_ref()
            .ok_or(MakeFunctionShapeError::NoFunctionData)?;
        FunctionShape::new(
            &function_data.shape_data_source(self.caller_substs, ctxt.tcx)?,
            ctxt.tcx,
        )
        .map_err(MakeFunctionShapeError::CheckOutlivesError)
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
        self.metadata.function_data.as_ref().map(|f| f.def_id)
    }
    pub fn substs(&self) -> Option<GenericArgsRef<'tcx>> {
        self.metadata.caller_substs
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
