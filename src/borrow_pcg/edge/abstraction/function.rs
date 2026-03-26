use std::{borrow::Cow, collections::HashMap, marker::PhantomData};

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
        infer::{infer::TyCtxtInferExt, traits::ObligationCause},
        middle::{
            mir::{self, Location},
            ty::{self, GenericArgsRef},
        },
        span::{DUMMY_SP, Span, def_id::LocalDefId},
        trait_selection::{
            infer::{RegionVariableOrigin, outlives::env::OutlivesEnvironment},
            traits::{NormalizeExt, ScrubbedTraitError, TraitEngine, TraitEngineExt},
        },
    },
    utils::{
        CompilerCtxt, DebugCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, HasTyCtxt, PcgPlace, Place,
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

impl<'tcx, Ctxt: HasTyCtxt<'tcx>> FunctionShapeDataSource<'tcx, Ctxt>
    for DefinedFnSigShapeDataSource<'tcx>
{
    fn input_tys(&self, ctxt: Ctxt) -> Vec<ty::Ty<'tcx>> {
        self.sig(ctxt.tcx()).inputs().to_vec()
    }

    fn output_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx> {
        self.sig(ctxt.tcx()).output()
    }

    fn outlives(
        &self,
        sup: PcgRegion<'tcx>,
        sub: PcgRegion<'tcx>,
        ctxt: Ctxt,
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
                ctxt.tcx(),
                sub.rust_region(ctxt.tcx()),
                sup.rust_region(ctxt.tcx()),
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

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> FunctionShapeDataSource<'tcx, Ctxt>
    for FnCallDataSource<'a, 'tcx>
{
    fn input_tys(&self, _ctxt: Ctxt) -> Vec<ty::Ty<'tcx>> {
        self.input_tys.clone()
    }
    fn output_ty(&self, _ctxt: Ctxt) -> ty::Ty<'tcx> {
        self.output_ty
    }
    fn outlives(
        &self,
        sup: PcgRegion<'tcx>,
        sub: PcgRegion<'tcx>,
        ctxt: Ctxt,
    ) -> Result<bool, CheckOutlivesError<'tcx>> {
        Ok(ctxt.bc().outlives(sup, sub, self.location))
    }
}

pub(crate) struct DefinedFnCallShapeDataSource<'a, 'tcx> {
    call: DefinedFnCallWithCallTys<'tcx>,
    /// Maps call-site regions to their corresponding normalized sig regions.
    /// Built by walking call-site types and normalized sig types in parallel.
    region_map: HashMap<PcgRegion<'tcx>, PcgRegion<'tcx>>,
    outlives: OutlivesEnvironment<'tcx>,
    _marker: PhantomData<&'a ()>,
}

impl<'a, 'tcx: 'a> DefinedFnCallShapeDataSource<'a, 'tcx> {
    #[rustversion::before(2025-05-24)]
    pub(crate) fn new(
        _call: DefinedFnCallWithCallTys<'tcx>,
        _tcx: ty::TyCtxt<'tcx>,
    ) -> Result<Self, MakeFunctionShapeError<'tcx>> {
        Err(MakeFunctionShapeError::UnsupportedRustVersion)
    }

    /// Builds a mapping from call-site regions to normalized sig regions by
    /// comparing regions at corresponding positions (by index) in the two types.
    fn build_region_map(
        call_tys: &[ty::Ty<'tcx>],
        call_result_ty: ty::Ty<'tcx>,
        normalized_sig: &ty::FnSig<'tcx>,
    ) -> HashMap<PcgRegion<'tcx>, PcgRegion<'tcx>> {
        use crate::borrow_pcg::visitor::extract_regions;
        let mut map = HashMap::default();
        for (call_ty, sig_ty) in call_tys.iter().zip(normalized_sig.inputs().iter()) {
            let call_regions = extract_regions(*call_ty);
            let sig_regions = extract_regions(*sig_ty);
            for (call_r, sig_r) in call_regions.iter().zip(sig_regions.iter()) {
                map.insert(*call_r, *sig_r);
            }
        }
        let call_result_regions = extract_regions(call_result_ty);
        let sig_result_regions = extract_regions(normalized_sig.output());
        for (call_r, sig_r) in call_result_regions.iter().zip(sig_result_regions.iter()) {
            map.insert(*call_r, *sig_r);
        }
        map
    }

    #[rustversion::since(2025-05-24)]
    #[allow(clippy::unnecessary_wraps)]
    pub(crate) fn new(
        call: DefinedFnCallWithCallTys<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<Self, MakeFunctionShapeError<'tcx>> {
        // Use the callee's typing env for outlives checks, since after mapping
        // regions back to identity regions, we need the callee's param env
        // constraints (e.g. `'b: 'a`).
        let callee_typing_env =
            ty::TypingEnv::post_analysis(ctxt.tcx(), call.fn_def_id());
        let (_, param_env) = ctxt
            .tcx()
            .infer_ctxt()
            .build_with_typing_env(callee_typing_env);
        let outlives = OutlivesEnvironment::from_normalized_bounds(
            param_env,
            vec![],
            vec![],
            HashSet::default(),
        );
        let normalized = call.defined_fn_call.normalized_sig(ctxt);
        let region_map = Self::build_region_map(
            &call.call_arg_tys,
            call.call_result_ty,
            &normalized,
        );
        Ok(Self {
            call,
            outlives,
            region_map,
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
    /// Maps a normalized sig region to the callee's identity region.
    fn normalized_to_identity(
        &self,
        region: PcgRegion<'tcx>,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Option<PcgRegion<'tcx>> {
        match region {
            PcgRegion::ReLateParam(_) | PcgRegion::ReStatic | PcgRegion::ReEarlyParam(_) => {
                Some(region)
            }
            PcgRegion::RegionVid(_) => {
                let index = self
                    .call
                    .caller_substs()
                    .regions()
                    .position(|r| PcgRegion::from(r) == region)?;
                let fn_ty = tcx.type_of(self.call.fn_def_id()).instantiate_identity();
                let ty::TyKind::FnDef(_def_id, identity_substs) = fn_ty.kind() else {
                    panic!("Expected a function type");
                };
                Some(identity_substs.region_at(index).into())
            }
            _ => None,
        }
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> FunctionShapeDataSource<'tcx, Ctxt>
    for DefinedFnCallShapeDataSource<'a, 'tcx>
{
    fn input_tys(&self, _ctxt: Ctxt) -> Vec<ty::Ty<'tcx>> {
        self.call.call_arg_tys.clone()
    }
    fn output_ty(&self, _ctxt: Ctxt) -> ty::Ty<'tcx> {
        self.call.call_result_ty
    }

    fn outlives(
        &self,
        sup: PcgRegion<'tcx>,
        sub: PcgRegion<'tcx>,
        ctxt: Ctxt,
    ) -> Result<bool, CheckOutlivesError<'tcx>> {
        if sup.is_static() || sup == sub {
            return Ok(true);
        }

        // Map call-site regions to normalized sig regions.
        let sup_norm = self.region_map.get(&sup).copied();
        let sub_norm = self.region_map.get(&sub).copied();

        // If both map to the same normalized region, they represent the same
        // lifetime in the callee's signature — outlives holds.
        if let (Some(s), Some(t)) = (sup_norm, sub_norm) {
            if s == t {
                return Ok(true);
            }
        }

        // Map to callee identity regions for param_env checking.
        // A region that can't be mapped to an identity region is nested inside
        // a type argument in caller_substs (e.g. 'a in Self = RefMut<'a, i32>).
        // Such regions are invisible to the callee's identity signature, so we
        // cannot check outlives precisely. Returning false here is imprecise —
        // the hidden region could flow to the result (e.g. deref_mut returns
        // data borrowed through 'a). The correct fix is implementing generic
        // lifetimes (doc § Signature Shape) where type parameters participate
        // in outlives relationships.
        // TODO: implement generic lifetimes to handle this correctly.
        let Some(sup_id) = sup_norm.and_then(|r| self.normalized_to_identity(r, ctxt.tcx()))
        else {
            return Ok(false);
        };
        let Some(sub_id) = sub_norm.and_then(|r| self.normalized_to_identity(r, ctxt.tcx()))
        else {
            return Ok(false);
        };
        if sup_id == sub_id {
            return Ok(true);
        }
        Ok(self.outlives.free_region_map().sub_free_regions(
            ctxt.tcx(),
            sub_id.rust_region(ctxt.tcx()),
            sup_id.rust_region(ctxt.tcx()),
        ))
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

pub struct DefinedFnCallWithCallTys<'tcx> {
    pub(crate) defined_fn_call: DefinedFnCall<'tcx>,
    pub(crate) call_arg_tys: Vec<ty::Ty<'tcx>>,
    pub(crate) call_result_ty: ty::Ty<'tcx>,
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for DefinedFnCallWithCallTys<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        DisplayOutput::join(
            vec![
                self.defined_fn_call.display_output(ctxt, mode),
                format!("call_arg_tys: {:?}", self.call_arg_tys).into(),
                format!("call_result_ty: {:?}", self.call_result_ty).into(),
            ],
            &DisplayOutput::NEWLINE,
        )
    }
}

impl<'tcx> DefinedFnCallWithCallTys<'tcx> {
    pub(crate) fn caller_def_id(&self) -> LocalDefId {
        self.defined_fn_call.caller_def_id
    }

    pub fn fn_def_id(&self) -> DefId {
        self.defined_fn_call.function_data.def_id
    }

    pub(crate) fn function_data(&self) -> FunctionData<'tcx> {
        self.defined_fn_call.function_data
    }

    pub fn caller_substs(&self) -> GenericArgsRef<'tcx> {
        self.defined_fn_call.caller_substs
    }

    pub(crate) fn new(
        defined_fn_call: DefinedFnCall<'tcx>,
        arg_tys: Vec<ty::Ty<'tcx>>,
        result_ty: ty::Ty<'tcx>,
    ) -> Self {
        Self {
            defined_fn_call,
            call_arg_tys: arg_tys,
            call_result_ty: result_ty,
        }
    }

    pub fn from_terminator<'a>(
        terminator: &mir::Terminator<'tcx>,
        caller_def_id: LocalDefId,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Option<Self>
    where
        'tcx: 'a,
    {
        if let mir::TerminatorKind::Call {
            ref func,
            ref args,
            destination,
            fn_span,
            ..
        } = terminator.kind
            && let ty::TyKind::FnDef(def_id, substs) = func.ty(ctxt.body(), ctxt.tcx()).kind()
        {
            let defined_fn_call =
                DefinedFnCall::new(FunctionData::new(*def_id), *substs, caller_def_id, fn_span);
            Some(Self {
                defined_fn_call,
                call_arg_tys: args
                    .iter()
                    .map(|arg| arg.node.ty(ctxt.body(), ctxt.tcx()))
                    .collect(),
                call_result_ty: destination.ty(ctxt.body(), ctxt.tcx()).ty,
            })
        } else {
            None
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub struct DefinedFnCall<'tcx> {
    pub(crate) function_data: FunctionData<'tcx>,
    pub(crate) caller_substs: GenericArgsRef<'tcx>,
    pub(crate) caller_def_id: LocalDefId,
    pub(crate) span: Span,
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt> for DefinedFnCall<'tcx> {
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        let identity_sig = self.function_data.identity_fn_sig(ctxt.tcx());
        let subst_sig = self.function_data.fn_sig(ctxt.tcx(), self.caller_substs);
        DisplayOutput::join(
            vec![
                "--------------------------------".into(),
                DisplayOutput::join(
                    vec![
                        self.function_data.display_output(ctxt, mode),
                        "at".into(),
                        format!("{:?}", self.span).into(),
                    ],
                    &DisplayOutput::SPACE,
                ),
                format!("identity_sig: {}", identity_sig).into(),
                format!("caller_substs: {:?}", self.caller_substs).into(),
                format!("subst_sig: {}", subst_sig).into(),
                format!("normalized_sig: {}", self.normalized_sig(ctxt)).into(),
                format!("callee_param_env: {:?}", self.callee_param_env(ctxt)).into(),
                format!("caller_def_id: {:?}", self.caller_def_id).into(),
                format!("span: {:?}", self.span).into(),
                "--------------------------------".into(),
            ],
            &"\n".into(),
        )
    }
}

impl<'tcx> DefinedFnCall<'tcx> {
    pub fn new(
        function_data: FunctionData<'tcx>,
        caller_substs: GenericArgsRef<'tcx>,
        caller_def_id: LocalDefId,
        span: Span,
    ) -> Self {
        Self {
            function_data,
            caller_substs,
            caller_def_id,
            span,
        }
    }

    pub(crate) fn callee_param_env<'a>(
        &self,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> ty::ParamEnv<'tcx>
    where
        'tcx: 'a,
    {
        ty::TypingEnv::post_analysis(ctxt.tcx(), self.function_data.def_id)
            .with_post_analysis_normalized(ctxt.tcx())
            .param_env
    }
    pub(crate) fn normalized_sig<'a>(
        &self,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> ty::FnSig<'tcx>
    where
        'tcx: 'a,
    {
        let caller_typing_env = ty::TypingEnv::post_analysis(ctxt.tcx(), self.caller_def_id)
            .with_post_analysis_normalized(ctxt.tcx());
        let (infcx, param_env) = ctxt
            .tcx()
            .infer_ctxt()
            .build_with_typing_env(caller_typing_env);
        let subst_sig = self.function_data.fn_sig(ctxt.tcx(), self.caller_substs);
        for _ in ctxt.bc_ctxt().borrow_checker().iter_region_vids() {
            infcx.next_region_var(RegionVariableOrigin::Misc(DUMMY_SP));
        }
        let mut fulfill_cx = <dyn TraitEngine<ScrubbedTraitError> as TraitEngineExt<
            ScrubbedTraitError,
        >>::new(&infcx);
        infcx
            .at(&ObligationCause::dummy(), param_env)
            .deeply_normalize(subst_sig, &mut *fulfill_cx)
            .unwrap()
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

    // pub fn shape(
    //     &self,
    //     ctxt: CompilerCtxt<'_, 'tcx>,
    // ) -> Result<FunctionShape, MakeFunctionShapeError<'tcx>> {
    //     let Some(call) = self.defined_fn_call.as_ref() else {
    //         return Err(MakeFunctionShapeError::NoFunctionData);
    //     };
    //     let data = DefinedFnCallShapeDataSource::new(
    //         *call,
    //         call.operand_tys.clone(),
    //         call.output_ty,
    //         ctxt,
    //     )?;
    //     FunctionShape::new(&data, ctxt).map_err(MakeFunctionShapeError::CheckOutlivesError)
    // }
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
