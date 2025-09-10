use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        abstraction::{FunctionShape, FunctionShapeDataSource},
        borrow_pcg_edge::{BlockedNode, LocalNode},
        domain::{FunctionCallAbstractionInput, FunctionCallAbstractionOutput},
        edge::abstraction::AbstractionBlockEdge,
        edge_data::{EdgeData, LabelEdgePlaces, LabelPlacePredicate},
        graph::coupling::HyperEdge,
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionPredicate,
            LabelLifetimeProjectionResult, PlaceLabeller,
        },
        region_projection::{LifetimeProjectionLabel, PcgRegion},
    },
    pcg::PcgNode,
    rustc_interface::{
        hir::def_id::DefId,
        infer::infer::TyCtxtInferExt,
        middle::{
            mir::Location,
            ty::{self, GenericArgsRef, TypeVisitableExt},
        },
        span::Span,
        trait_selection::infer::outlives::env::OutlivesEnvironment,
    },
    utils::{CompilerCtxt, display::DisplayWithCompilerCtxt, validity::HasValidityCheck},
};

#[rustversion::since(2025-05-24)]
use crate::rustc_interface::trait_selection::regions::OutlivesEnvironmentBuildExt;

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub struct FunctionData<'tcx> {
    pub(crate) def_id: DefId,
    pub(crate) substs: GenericArgsRef<'tcx>,
}

pub(crate) struct FunctionDataShapeDataSource<'tcx> {
    input_tys: Vec<ty::Ty<'tcx>>,
    output_ty: ty::Ty<'tcx>,
    outlives: OutlivesEnvironment<'tcx>,
}

#[allow(unused)]
#[derive(Debug)]
pub enum MakeFunctionShapeError {
    ContainsAliasType,
    UnsupportedRustVersion,
}

impl<'tcx> FunctionDataShapeDataSource<'tcx> {
    #[rustversion::before(2025-05-24)]
    pub(crate) fn new(
        _data: FunctionData<'tcx>,
        _ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<Self, MakeFunctionShapeError> {
        Err(MakeFunctionShapeError::UnsupportedRustVersion)
    }

    #[rustversion::since(2025-05-24)]
    pub(crate) fn new(
        data: FunctionData<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<Self, MakeFunctionShapeError> {
        tracing::debug!("Base Sig: {:#?}", data.fn_sig(ctxt));
        let sig = data.instantiated_fn_sig(ctxt);
        tracing::debug!("Instantiated Sig: {:#?}", sig);
        let sig = ctxt.tcx().liberate_late_bound_regions(data.def_id, sig);
        tracing::debug!("Liberated Sig: {:#?}", sig);
        let typing_env = ty::TypingEnv::post_analysis(ctxt.tcx(), ctxt.def_id());
        let (infcx, param_env) = ctxt.tcx().infer_ctxt().build_with_typing_env(typing_env);
        if sig.has_aliases() {
            return Err(MakeFunctionShapeError::ContainsAliasType);
        }
        tracing::debug!("Normalized sig: {:#?}", sig);
        let outlives = OutlivesEnvironment::new(&infcx, ctxt.def_id(), param_env, vec![]);
        Ok(Self {
            input_tys: sig.inputs().to_vec(),
            output_ty: sig.output(),
            outlives,
        })
    }
}

impl<'tcx> FunctionData<'tcx> {
    pub(crate) fn fn_sig(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> ty::EarlyBinder<'tcx, ty::Binder<'tcx, ty::FnSig<'tcx>>> {
        ctxt.tcx().fn_sig(self.def_id)
    }

    pub(crate) fn instantiated_fn_sig(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> ty::Binder<'tcx, ty::FnSig<'tcx>> {
        ctxt.tcx()
            .fn_sig(self.def_id)
            .instantiate(ctxt.tcx(), self.substs)
    }
}

impl<'tcx> FunctionShapeDataSource<'tcx> for FunctionDataShapeDataSource<'tcx> {
    fn input_tys(&self, _ctxt: CompilerCtxt<'_, 'tcx>) -> Vec<ty::Ty<'tcx>> {
        self.input_tys.clone()
    }
    fn output_ty(&self, _ctxt: CompilerCtxt<'_, 'tcx>) -> ty::Ty<'tcx> {
        self.output_ty
    }

    fn outlives(&self, sup: PcgRegion, sub: PcgRegion, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        if sup.is_static() || sup == sub {
            return true;
        }
        tracing::debug!("Check if:\n{:?}\noutlives\n{:?}", sup, sub);
        match (sup, sub) {
            (PcgRegion::RegionVid(_), PcgRegion::RegionVid(_) | PcgRegion::ReStatic) => {
                ctxt.bc.outlives_everywhere(sup, sub)
            }
            (PcgRegion::ReLateParam(_), PcgRegion::RegionVid(_)) => false,
            (PcgRegion::RegionVid(_), PcgRegion::ReLateParam(_)) => true,
            _ => self.outlives.free_region_map().sub_free_regions(
                ctxt.tcx(),
                sup.rust_region(ctxt),
                sub.rust_region(ctxt),
            ),
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
        span: Span,
    ) -> Self {
        Self {
            function_data: FunctionData { def_id, substs },
            operand_tys,
            span,
        }
    }

    pub(crate) fn shape(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<FunctionShape<'tcx>, MakeFunctionShapeError> {
        let data = FunctionDataShapeDataSource::new(self.function_data, ctxt)?;
        Ok(FunctionShape::new(&data, ctxt))
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

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub struct FunctionCallAbstractionEdgeMetadata<'tcx> {
    location: Location,
    pub(crate) function_data: Option<FunctionData<'tcx>>,
}

pub type FunctionCallAbstraction<'tcx> = AbstractionBlockEdgeWithMetadata<
    FunctionCallAbstractionEdgeMetadata<'tcx>,
    FunctionCallAbstractionEdge<'tcx>,
>;

impl<'tcx> LabelLifetimeProjection<'tcx> for FunctionCallAbstraction<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        predicate: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        repacker: CompilerCtxt<'_, 'tcx>,
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

impl<'tcx> HasValidityCheck<'tcx> for FunctionCallAbstraction<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.edge.check_validity(ctxt)
    }
}

impl<'tcx, 'a> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for FunctionCallAbstraction<'tcx>
{
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        format!(
            "call{} at {:?}: {}",
            if let Some(function_data) = &self.metadata.function_data {
                format!(" {}", ctxt.tcx().def_path_str(function_data.def_id))
            } else {
                "".to_string()
            },
            self.metadata.location,
            self.edge.to_short_string(ctxt)
        )
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
        location: Location,
        function_data: Option<FunctionData<'tcx>>,
        edge: AbstractionBlockEdge<
            'tcx,
            FunctionCallAbstractionInput<'tcx>,
            FunctionCallAbstractionOutput<'tcx>,
        >,
    ) -> Self {
        Self {
            metadata: FunctionCallAbstractionEdgeMetadata {
                location,
                function_data,
            },
            edge,
        }
    }
}
