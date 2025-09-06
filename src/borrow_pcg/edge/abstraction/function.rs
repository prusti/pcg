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
            infer,
            traits::{NormalizeExt, ObligationCtxt},
        },
    },
    utils::{CompilerCtxt, display::DisplayWithCompilerCtxt, validity::HasValidityCheck},
};

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub struct FunctionData<'tcx> {
    pub(crate) def_id: DefId,
    pub(crate) substs: GenericArgsRef<'tcx>,
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

    pub(crate) fn instantiated_sig(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> ty::Binder<'tcx, ty::FnSig<'tcx>> {
        let fn_sig = ctxt.tcx().fn_sig(self.def_id());
        fn_sig.instantiate(ctxt.tcx(), self.substs())
    }

    pub(crate) fn fully_normalized_sig(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> ty::FnSig<'tcx> {
        let fn_sig = self.instantiated_sig(ctxt);
        let cause = ObligationCause::dummy();
        let (infcx, param_env) = ctxt
            .tcx()
            .infer_ctxt()
            .build_with_typing_env(ty::TypingEnv::post_analysis(ctxt.tcx(), ctxt.def_id()));
        let fn_sig = infcx
            .at(&cause, param_env)
            .query_normalize(fn_sig)
            .unwrap()
            .value;
        let fv_sig = infcx.instantiate_binder_with_fresh_vars(
            self.span,
            infer::BoundRegionConversionTime::FnCall,
            fn_sig,
        );
        let octxt = ObligationCtxt::new(&infcx);
        let infcx = infcx.at(&cause, param_env);
        for (op_ty, sig_ty) in self.operand_tys.iter().zip(fv_sig.inputs().iter()) {
            if !sig_ty.has_bound_regions() {
                continue;
            }
            tracing::info!("Require {:?} <: {:?}", op_ty, sig_ty);
            let obligations = infcx
                .sub(infer::DefineOpaqueTypes::No, *op_ty, *sig_ty)
                .unwrap()
                .obligations;
            octxt.register_obligations(obligations);
        }
        tracing::info!("Deeply normalize {:?}", fv_sig);
        octxt.deeply_normalize(&cause, param_env, fv_sig).unwrap()
    }

    pub(crate) fn shape(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> FunctionShape<'tcx> {
        let sig = self.fully_normalized_sig(ctxt);
        FunctionShape::new(&sig, ctxt)
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
