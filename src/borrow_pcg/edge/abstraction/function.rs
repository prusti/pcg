use crate::borrow_pcg::abstraction::FunctionShapeDataSource;
use crate::borrow_pcg::region_projection::PcgRegion;
use crate::rustc_interface::infer::infer::TyCtxtInferExt;
use crate::rustc_interface::infer::traits::ObligationCause;
use crate::rustc_interface::trait_selection::traits::query::normalize::QueryNormalizeExt;
use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        abstraction::FunctionShape,
        borrow_pcg_edge::{BlockedNode, LocalNode},
        domain::{FunctionCallAbstractionInput, FunctionCallAbstractionOutput},
        edge::abstraction::AbstractionBlockEdge,
        edge_data::{EdgeData, LabelEdgePlaces, LabelPlacePredicate},
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionPredicate,
            LabelLifetimeProjectionResult, PlaceLabeller,
        },
        region_projection::LifetimeProjectionLabel,
    },
    pcg::PcgNode,
    rustc_interface::{
        hir::def_id::DefId,
        middle::{
            mir::Location,
            ty::{self, GenericArgsRef, TypeVisitableExt},
        },
        span::Span,
        trait_selection::{
            infer::{self, InferCtxt, outlives::env::OutlivesEnvironment},
            regions::OutlivesEnvironmentBuildExt,
            traits::{
                FulfillmentContext, FulfillmentError, NormalizeExt, ObligationCtxt, TraitEngine,
                TraitEngineExt,
            },
        },
    },
    utils::{CompilerCtxt, display::DisplayWithCompilerCtxt, validity::HasValidityCheck},
};

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

#[derive(Debug)]
pub enum MakeFunctionShapeError {
    ContainsAliasType,
}

impl<'tcx> FunctionDataShapeDataSource<'tcx> {
    pub(crate) fn new(
        data: FunctionData<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<Self, MakeFunctionShapeError> {
        tracing::info!("Base Sig: {:#?}", data.fn_sig(ctxt));
        let sig = data.instantiated_fn_sig(ctxt);
        tracing::info!("Instantiated Sig: {:#?}", sig);
        let sig = ctxt.tcx().liberate_late_bound_regions(data.def_id, sig);
        tracing::info!("Liberated Sig: {:#?}", sig);
        let typing_env = ty::TypingEnv::post_analysis(ctxt.tcx(), ctxt.def_id());
        let (infcx, param_env) = ctxt.tcx().infer_ctxt().build_with_typing_env(typing_env);
        if sig.has_aliases() {
            return Err(MakeFunctionShapeError::ContainsAliasType);
        }
        // // let obligation_ctxt = ObligationCtxt::new(&infcx);
        // // let sig = obligation_ctxt
        // //     .deeply_normalize(&ObligationCause::dummy(), param_env, sig)
        // //     .unwrap();
        // let sig = infcx
        //     .at(&ObligationCause::dummy(), param_env)
        //     .normalize(sig)
        //     .value;
        tracing::info!("Normalized sig: {:#?}", sig);
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
        tracing::info!("Check if:\n{:?}\noutlives\n{:?}", sup, sub);
        match (sup, sub) {
            (PcgRegion::RegionVid(_), PcgRegion::RegionVid(_)) => {
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

    pub(crate) fn def_id(&self) -> DefId {
        self.function_data.def_id
    }
    pub(crate) fn substs(&self) -> GenericArgsRef<'tcx> {
        self.function_data.substs
    }

    // pub(crate) fn instantiated_sig(
    //     &self,
    //     ctxt: CompilerCtxt<'_, 'tcx>,
    // ) -> ty::Binder<'tcx, ty::FnSig<'tcx>> {
    //     let fn_sig = ctxt.tcx().fn_sig(self.def_id());
    //     fn_sig.instantiate(ctxt.tcx(), self.substs())
    // }

    // fn normalize(
    //     &self,
    //     infcx: &InferCtxt<'tcx>,
    //     param_env: ty::ParamEnv<'tcx>,
    //     fn_sig: ty::FnSig<'tcx>,
    // ) -> ty::FnSig<'tcx> {
    //     tracing::info!("Normalize {:?}", fn_sig);
    //     let cause = ObligationCause::dummy();
    //     let octxt = ObligationCtxt::new(&infcx);
    //     let infcx = infcx.at(&cause, param_env);
    //     for (op_ty, sig_ty) in self.operand_tys.iter().zip(fn_sig.inputs().iter()) {
    //         tracing::info!("Require {:?} <: {:?}", op_ty, sig_ty);
    //         let obligations = infcx
    //             .sub(infer::DefineOpaqueTypes::No, *op_ty, *sig_ty)
    //             .unwrap()
    //             .obligations;
    //         octxt.register_obligations(obligations);
    //     }
    //     tracing::info!("Deeply normalize {:?}", fn_sig);
    //     octxt.deeply_normalize(&cause, param_env, fn_sig).unwrap()
    // }

    // pub(crate) fn fully_normalized_sig(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> ty::FnSig<'tcx> {
    //     let fn_sig = self.instantiated_sig(ctxt);
    //     tracing::info!("Instantiated sig: {:?}", fn_sig);
    //     let cause = ObligationCause::dummy();
    //     let (infcx, param_env) = ctxt
    //         .tcx()
    //         .infer_ctxt()
    //         .build_with_typing_env(ty::TypingEnv::post_analysis(ctxt.tcx(), ctxt.def_id()));
    //     let fn_sig = infcx
    //         .at(&cause, param_env)
    //         .query_normalize(fn_sig)
    //         .unwrap()
    //         .value;
    //     tracing::info!("Normalized sig: {:?}", fn_sig);
    //     // let fv_sig = infcx.instantiate_binder_with_fresh_vars(
    //     //     self.span,
    //     //     infer::BoundRegionConversionTime::FnCall,
    //     //     fn_sig,
    //     // );
    //     // self.normalize(infcx, param_env, fv_sig)

    //     infcx.enter_forall(fn_sig, |fv_sig| self.normalize(&infcx, param_env, fv_sig))
    // }

    pub(crate) fn shape(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<FunctionShape<'tcx>, MakeFunctionShapeError> {
        let data = FunctionDataShapeDataSource::new(self.function_data, ctxt)?;
        Ok(FunctionShape::new(&data, ctxt))
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct FunctionCallAbstraction<'tcx> {
    location: Location,
    /// This may be `None` if the call is to a function pointer
    function_data: Option<FunctionData<'tcx>>,
    edge: AbstractionBlockEdge<
        'tcx,
        FunctionCallAbstractionInput<'tcx>,
        FunctionCallAbstractionOutput<'tcx>,
    >,
}

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
            if let Some(function_data) = &self.function_data {
                format!(" {}", ctxt.tcx().def_path_str(function_data.def_id))
            } else {
                "".to_string()
            },
            self.location,
            self.edge.to_short_string(ctxt)
        )
    }
}

impl<'tcx> FunctionCallAbstraction<'tcx> {
    pub fn def_id(&self) -> Option<DefId> {
        self.function_data.as_ref().map(|f| f.def_id)
    }
    pub fn substs(&self) -> Option<GenericArgsRef<'tcx>> {
        self.function_data.as_ref().map(|f| f.substs)
    }

    pub fn location(&self) -> Location {
        self.location
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
            location,
            function_data,
            edge,
        }
    }
}
