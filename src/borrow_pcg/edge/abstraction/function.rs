use std::borrow::Cow;

use derive_more::{Deref, DerefMut};

use crate::{
    borrow_pcg::{
        FunctionData,
        borrow_pcg_edge::{BlockedNode, LocalNode},
        domain::{FunctionCallAbstractionInput, FunctionCallAbstractionOutput},
        edge::abstraction::AbstractionBlockEdge,
        edge_data::{
            EdgeData, LabelEdgeLifetimeProjections, LabelEdgePlaces, LabelNodePredicate,
            NodeReplacement,
        },
        has_pcs_elem::{LabelLifetimeProjectionResult, PlaceLabeller},
        region_projection::LifetimeProjectionLabel,
    },
    coupling::CoupledEdgeKind,
    pcg::PcgNodeWithPlace,
    rustc_interface::{
        BoundVariableKind, fn_def_args,
        hir::def_id::DefId,
        middle::{
            mir::{self, Location},
            ty::{self, GenericArgsRef},
        },
        skip_normalization,
        span::{Span, def_id::LocalDefId},
    },
    utils::{
        DebugCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, PcgPlace, Place,
        data_structures::HashSet,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        validity::{HasValidityCheck, has_validity_check_node_wrapper},
    },
};

use crate::coupling::HyperEdge;

impl<'tcx> FunctionData<'tcx> {
    #[must_use]
    pub fn identity_fn_sig(self, tcx: ty::TyCtxt<'tcx>) -> ty::FnSig<'tcx> {
        let fn_sig = if tcx.is_closure_like(self.def_id) {
            let ty::TyKind::Closure(_, args) =
                skip_normalization(tcx.type_of(self.def_id).instantiate_identity()).kind()
            else {
                unreachable!();
            };
            self.closure_fn_sig(tcx, args)
        } else {
            skip_normalization(tcx.fn_sig(self.def_id).instantiate_identity())
        };
        tcx.liberate_late_bound_regions(self.def_id, fn_sig)
    }

    /// Returns the function signature instantiated with the given substs (but
    /// not normalized).
    #[must_use]
    pub fn fn_sig(self, tcx: ty::TyCtxt<'tcx>, substs: GenericArgsRef<'tcx>) -> ty::FnSig<'tcx> {
        let fn_sig = if tcx.is_closure_like(self.def_id) {
            self.closure_fn_sig(tcx, substs)
        } else {
            skip_normalization(tcx.fn_sig(self.def_id).instantiate(tcx, substs))
        };
        tcx.liberate_late_bound_regions(self.def_id, fn_sig)
    }

    /// The signature of a closure body: the environment (taken by value or by
    /// reference, per the closure kind) followed by the untupled arguments.
    /// Mirrors the construction in rustc's `UniversalRegions` (borrowck),
    /// which is not exposed as a query.
    fn closure_fn_sig(
        self,
        tcx: ty::TyCtxt<'tcx>,
        args: GenericArgsRef<'tcx>,
    ) -> ty::PolyFnSig<'tcx> {
        let (args, capture_regions) = renumbered_captures(tcx, args);
        let closure = args.as_closure();
        let closure_sig = closure.sig();
        // Typeck also erases the regions of the closure's own parameter and
        // return types (not just its captures, see `renumbered_captures`
        // above). Give each erased region its own fresh bound var, bound by
        // this same signature, so they become distinct universal regions
        // once liberated instead of collapsing to a single erased region.
        let param_base_vars = closure_sig.bound_vars().len() + capture_regions.len();
        let mut param_regions = Vec::new();
        let sig = ty::fold_regions(tcx, closure_sig.skip_binder(), |region, _| {
            if !region.is_erased() {
                return region;
            }
            let var = ty::BoundVar::from_usize(param_base_vars + param_regions.len());
            param_regions.push(ty::BoundVariableKind::Region(ty::BoundRegionKind::Anon));
            ty::Region::new_bound(
                tcx,
                ty::INNERMOST,
                ty::BoundRegion {
                    var,
                    kind: ty::BoundRegionKind::Anon,
                },
            )
        });
        let bound_vars = tcx.mk_bound_variable_kinds_from_iter(
            closure_sig
                .bound_vars()
                .iter()
                .chain(capture_regions)
                .chain(param_regions)
                .chain(std::iter::once(ty::BoundVariableKind::Region(
                    ty::BoundRegionKind::ClosureEnv,
                ))),
        );
        let env_region = ty::Region::new_bound(
            tcx,
            ty::INNERMOST,
            ty::BoundRegion {
                var: ty::BoundVar::from_usize(bound_vars.len() - 1),
                kind: ty::BoundRegionKind::ClosureEnv,
            },
        );
        let closure_ty = ty::Ty::new_closure(tcx, self.def_id, args);
        let env_ty = tcx.closure_env_ty(closure_ty, closure.kind(), env_region);
        let inputs = std::iter::once(env_ty).chain(sig.inputs()[0].tuple_fields());
        #[rustversion::since(2026-04-19)]
        let fn_sig = tcx.mk_fn_sig(inputs, sig.output(), sig.fn_sig_kind);
        #[rustversion::before(2026-04-19)]
        let fn_sig = tcx.mk_fn_sig(inputs, sig.output(), sig.c_variadic, sig.safety, sig.abi);
        ty::Binder::bind_with_vars(fn_sig, bound_vars)
    }
}

/// The closure arguments with the regions of the captures restored, together
/// with the regions bound for them. The caller must bind these immediately
/// after the ones the closure signature binds.
///
/// Typeck erases the regions of the captures, so `tcx.type_of` gives
/// `ReErased` where borrowck sees universal regions inherited from the
/// enclosing function. Which region a capture had is not recoverable from the
/// type alone: borrowck renumbers them into fresh inference variables and
/// re-infers them (`UniversalRegions::defining_ty`). Lacking an inference
/// context, we bind each as its own late-bound region instead, so that
/// liberating the signature makes them distinct universal regions of the
/// closure, as it does for the elided lifetimes of a `fn`.
fn renumbered_captures<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    args: GenericArgsRef<'tcx>,
) -> (GenericArgsRef<'tcx>, Vec<BoundVariableKind<'tcx>>) {
    let closure = args.as_closure();
    let mut regions = Vec::new();
    // Only the captures are renumbered: the regions of the signature are
    // bound by it, and those of the parent arguments are its parameters.
    // The captures are a tuple of types, so no binder is crossed and the
    // fresh regions are bound by the signature that the caller builds.
    let upvars = ty::fold_regions(tcx, closure.tupled_upvars_ty(), |region, _| {
        if !region.is_erased() {
            return region;
        }
        let var = ty::BoundVar::from_usize(closure.sig().bound_vars().len() + regions.len());
        regions.push(ty::BoundVariableKind::Region(ty::BoundRegionKind::Anon));
        ty::Region::new_bound(
            tcx,
            ty::INNERMOST,
            ty::BoundRegion {
                var,
                kind: ty::BoundRegionKind::Anon,
            },
        )
    });
    let args = tcx.mk_args_from_iter(closure.parent_args().iter().copied().chain([
        closure.kind_ty().into(),
        closure.sig_as_fn_ptr_ty().into(),
        upvars.into(),
    ]));
    (args, regions)
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
    #[must_use]
    pub fn fn_def_id(&self) -> DefId {
        self.defined_fn_call.function_data.def_id
    }

    #[must_use]
    pub fn caller_substs(&self) -> GenericArgsRef<'tcx> {
        self.defined_fn_call.caller_substs
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
            let defined_fn_call = DefinedFnCall::new(
                FunctionData::new(*def_id),
                fn_def_args(substs),
                caller_def_id,
                fn_span,
            );
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

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for DefinedFnCall<'tcx>
{
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
                format!("identity_sig: {identity_sig}").into(),
                format!("caller_substs: {:?}", self.caller_substs).into(),
                format!("subst_sig: {subst_sig}").into(),
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
    #[must_use]
    pub fn location(&self) -> Location {
        self.location
    }

    #[must_use]
    pub fn def_id(&self) -> Option<DefId> {
        self.defined_fn_call
            .as_ref()
            .map(|f| f.function_data.def_id)
    }

    #[must_use]
    pub fn function_data(&self) -> Option<FunctionData<'tcx>> {
        self.defined_fn_call.as_ref().map(|f| f.function_data)
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

impl<'tcx, Ctxt: DebugCtxt, P: PcgPlace<'tcx, Ctxt>> LabelEdgePlaces<'tcx, Ctxt, P>
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
    ) -> Box<dyn Iterator<Item = PcgNodeWithPlace<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        self.edge.blocked_nodes(ctxt)
    }

    fn blocked_by_nodes<'slf>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Box<dyn Iterator<Item = LocalNode<'tcx, P>> + 'slf>
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
    #[must_use]
    pub fn def_id(&self) -> Option<DefId> {
        self.metadata.function_data().as_ref().map(|f| f.def_id)
    }
    #[must_use]
    pub fn substs(&self) -> Option<GenericArgsRef<'tcx>> {
        self.metadata
            .defined_fn_call
            .as_ref()
            .map(|f| f.caller_substs)
    }

    #[must_use]
    pub fn location(&self) -> Location {
        self.metadata.location
    }

    #[must_use]
    pub fn edge(
        &self,
    ) -> &AbstractionBlockEdge<
        'tcx,
        FunctionCallAbstractionInput<'tcx>,
        FunctionCallAbstractionOutput<'tcx>,
    > {
        &self.edge
    }

    #[must_use]
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
