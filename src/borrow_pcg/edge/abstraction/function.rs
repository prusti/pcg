use std::borrow::Cow;

use crate::{
    borrow_pcg::{
        FunctionData,
        abstraction::{
            CheckOutlivesError, FunctionShape, FunctionShapeDataSource, MakeFunctionShapeError,
        },
        borrow_pcg_edge::{BlockedNode, LocalNode},
        domain::{FunctionCallAbstractionInput, FunctionCallAbstractionOutput},
        edge::abstraction::AbstractionBlockEdge,
        edge_data::{EdgeData, LabelEdgePlaces, LabelPlacePredicate},
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionPredicate,
            LabelLifetimeProjectionResult, PlaceLabeller,
        },
        region_projection::{LifetimeProjectionLabel, PcgRegion},
    },
    coupling::CoupledEdgeKind,
    pcg::PcgNode,
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
    utils::display::{DisplayOutput, OutputMode},
    utils::{
        CompilerCtxt, HasBorrowCheckerCtxt, display::DisplayWithCtxt, validity::HasValidityCheck,
    },
};

use crate::coupling::HyperEdge;

#[rustversion::since(2025-05-24)]
use crate::rustc_interface::trait_selection::regions::OutlivesEnvironmentBuildExt;

pub struct FunctionDataShapeDataSource<'tcx> {
    input_tys: Vec<ty::Ty<'tcx>>,
    output_ty: ty::Ty<'tcx>,
    outlives: OutlivesEnvironment<'tcx>,
}

impl<'tcx> FunctionDataShapeDataSource<'tcx> {
    #[rustversion::before(2025-05-24)]
    pub(crate) fn new(
        _data: FunctionData<'tcx>,
        _ctxt: ty::TyCtxt<'tcx>,
    ) -> Result<Self, MakeFunctionShapeError> {
        Err(MakeFunctionShapeError::UnsupportedRustVersion)
    }

    #[rustversion::since(2025-05-24)]
    pub(crate) fn new(
        data: FunctionData<'tcx>,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Result<Self, MakeFunctionShapeError> {
        let sig = data.instantiated_fn_sig(tcx);
        tracing::debug!("Liberated Sig: {:#?}", sig);
        let typing_env = ty::TypingEnv::post_analysis(tcx, data.def_id);
        let (infcx, param_env) = tcx.infer_ctxt().build_with_typing_env(typing_env);
        if sig.has_aliases() {
            return Err(MakeFunctionShapeError::ContainsAliasType);
        }
        tracing::debug!("Normalized sig: {:#?}", sig);
        let outlives = match data.caller_def_id {
            Some(caller_def_id) => {
                OutlivesEnvironment::new(&infcx, caller_def_id, param_env, vec![])
            }
            None => OutlivesEnvironment::from_normalized_bounds(
                param_env,
                vec![],
                vec![],
                Default::default(),
            ),
        };
        Ok(Self {
            input_tys: sig.inputs().to_vec(),
            output_ty: sig.output(),
            outlives,
        })
    }
}

impl<'tcx> FunctionData<'tcx> {
    pub fn instantiated_fn_sig(&self, tcx: ty::TyCtxt<'tcx>) -> ty::FnSig<'tcx> {
        let fn_sig = tcx.fn_sig(self.def_id).instantiate(tcx, self.substs);
        tcx.liberate_late_bound_regions(self.def_id, fn_sig)
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
        tracing::debug!("Check if:\n{:?}\noutlives\n{:?}", sup, sub);
        match (sup, sub) {
            (PcgRegion::RegionVid(_), PcgRegion::RegionVid(_) | PcgRegion::ReStatic) => {
                Err(CheckOutlivesError::CannotCompareRegions { sup, sub })
            }
            (PcgRegion::ReLateParam(_), PcgRegion::RegionVid(_)) => Ok(false),
            (PcgRegion::RegionVid(_), PcgRegion::ReLateParam(_)) => Ok(true),
            _ => Ok(self.outlives.free_region_map().sub_free_regions(
                ctxt,
                sup.rust_region(ctxt),
                sub.rust_region(ctxt),
            )),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct FunctionCallData<'tcx> {
    pub(crate) function_data: FunctionData<'tcx>,
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
            function_data: FunctionData::new(def_id, substs, Some(caller_def_id)),
            operand_tys,
            span,
        }
    }

    pub(crate) fn shape(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<FunctionShape, MakeFunctionShapeError> {
        let data = FunctionDataShapeDataSource::new(self.function_data, ctxt.tcx)?;
        FunctionShape::new(&data, ctxt.tcx).map_err(MakeFunctionShapeError::CheckOutlivesError)
    }
}

pub(crate) type FunctionCallAbstractionEdge<'tcx> = AbstractionBlockEdge<
    'tcx,
    FunctionCallAbstractionInput<'tcx>,
    FunctionCallAbstractionOutput<'tcx>,
>;

impl<'tcx> FunctionCallAbstractionEdge<'tcx> {
    pub fn to_hyper_edge(
        &self,
    ) -> HyperEdge<FunctionCallAbstractionInput<'tcx>, FunctionCallAbstractionOutput<'tcx>> {
        HyperEdge::new(vec![self.input], vec![self.output])
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct AbstractionBlockEdgeWithMetadata<Metadata, Edge> {
    pub(crate) metadata: Metadata,
    pub(crate) edge: Edge,
}

impl<'tcx, Metadata, Input: Copy, Output: Copy>
    AbstractionBlockEdgeWithMetadata<Metadata, AbstractionBlockEdge<'tcx, Input, Output>>
{
    pub(crate) fn into_singleton_coupled_edge(self) -> CoupledEdgeKind<Metadata, Input, Output> {
        CoupledEdgeKind::new(self.metadata, self.edge.to_singleton_hyper_edge())
    }
}
#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub struct FunctionCallAbstractionEdgeMetadata<'tcx> {
    pub(crate) location: Location,
    pub(crate) function_data: Option<FunctionData<'tcx>>,
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
                    "".to_string()
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
        FunctionShape::new(&function_data.shape_data_source(ctxt.tcx)?, ctxt.tcx)
            .map_err(MakeFunctionShapeError::CheckOutlivesError)
    }
}

pub type FunctionCallAbstraction<'tcx> = AbstractionBlockEdgeWithMetadata<
    FunctionCallAbstractionEdgeMetadata<'tcx>,
    FunctionCallAbstractionEdge<'tcx>,
>;

impl<'a, 'tcx> LabelLifetimeProjection<'a, 'tcx> for FunctionCallAbstraction<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        predicate: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        repacker: CompilerCtxt<'a, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        self.edge
            .label_lifetime_projection(predicate, label, repacker)
    }
}

impl<'tcx> LabelEdgePlaces<'tcx> for FunctionCallAbstraction<'tcx> {
    fn label_blocked_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.edge.label_blocked_places(predicate, labeller, ctxt)
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.edge.label_blocked_by_places(predicate, labeller, ctxt)
    }
}

impl<'tcx> EdgeData<'tcx> for FunctionCallAbstraction<'tcx> {
    fn blocks_node<'slf>(&self, node: BlockedNode<'tcx>, repacker: CompilerCtxt<'_, 'tcx>) -> bool {
        self.edge.blocks_node(node, repacker)
    }

    fn blocked_nodes<'slf, BC: Copy>(
        &'slf self,
        ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = PcgNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        self.edge.blocked_nodes(ctxt)
    }

    fn blocked_by_nodes<'slf, 'mir: 'slf, BC: Copy + 'slf>(
        &'slf self,
        repacker: CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx>> + 'slf>
    where
        'tcx: 'mir,
    {
        self.edge.blocked_by_nodes(repacker)
    }
}

impl<'tcx> HasValidityCheck<'_, 'tcx> for FunctionCallAbstraction<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.edge.check_validity(ctxt)
    }
}

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
        self.metadata.function_data.as_ref().map(|f| f.substs)
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
