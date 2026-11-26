use std::{
    collections::{BTreeSet, HashSet},
    marker::PhantomData,
};

use derive_more::{Deref, From};

pub(crate) mod spec;

use crate::{
    HasSettings,
    borrow_pcg::{
        abstraction::spec::{CallSpecQuery, Callee, call_spec, check_call_spec},
        edge::abstraction::{
            AbstractionBlockEdge,
            function::{DefinedFnCall, DefinedFnCallWithCallTys},
        },
        region_projection::{
            Generalized, HasTy, LifetimeProjection, RegionIdxMarker, default_region_display_output,
        },
        visitor::LifetimeEnv,
    },
    coupling::{CoupleAbstractionError, CoupledEdgesData},
    rustc_interface::{
        index::Idx,
        middle::{
            mir,
            ty::{self, GenericArgsRef},
        },
        span::def_id::DefId,
    },
    utils::{
        self, HasBorrowCheckerCtxt, HasLifetimeEnv, HasTyCtxt,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
    },
    validity_checks_enabled,
};

#[derive(Deref, From, Copy, Clone, Debug, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct ArgIdx(usize);

impl crate::Sealed for ArgIdx {}

impl<'tcx, Ctxt: HasTyCtxt<'tcx>> HasTy<'tcx, (FunctionData<'tcx>, Ctxt)> for ArgIdx {
    fn rust_ty(&self, (function_data, ctxt): (FunctionData<'tcx>, Ctxt)) -> ty::Ty<'tcx> {
        function_data.identity_fn_sig(ctxt.tcx()).inputs()[self.0]
    }
}

impl<Ctxt> DisplayWithCtxt<Ctxt> for ArgIdx {
    fn display_output(&self, _ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        self.to_string().into()
    }
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum ArgIdxOrResult {
    Argument(ArgIdx),
    Result,
}

impl crate::Sealed for ArgIdxOrResult {}

impl<'tcx> DisplayWithCtxt<(FunctionData<'tcx>, ty::TyCtxt<'tcx>)> for ty::RegionVid {
    fn display_output(
        &self,
        _ctxt: (FunctionData<'tcx>, ty::TyCtxt<'tcx>),
        _mode: OutputMode,
    ) -> DisplayOutput {
        default_region_display_output(*self)
    }
}

impl<'tcx, Ctxt: HasTyCtxt<'tcx>> HasTy<'tcx, (FunctionData<'tcx>, Ctxt)> for ArgIdxOrResult {
    fn rust_ty(&self, (function_data, ctxt): (FunctionData<'tcx>, Ctxt)) -> ty::Ty<'tcx> {
        match self {
            ArgIdxOrResult::Argument(arg) => arg.rust_ty((function_data, ctxt.tcx())),
            ArgIdxOrResult::Result => function_data.identity_fn_sig(ctxt.tcx()).output(),
        }
    }
}

impl<Ctxt> DisplayWithCtxt<Ctxt> for ArgIdxOrResult {
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        match self {
            ArgIdxOrResult::Argument(arg) => arg.display_output(ctxt, mode),
            ArgIdxOrResult::Result => "result".into(),
        }
    }
}

#[derive(Copy, Clone)]
pub(crate) struct FunctionCall<'a, 'tcx> {
    pub(crate) defined: Option<DefinedFnCall<'tcx>>,
    pub(crate) location: mir::Location,
    pub(crate) inputs: &'a [&'a mir::Operand<'tcx>],
    pub(crate) output: utils::Place<'tcx>,
}

impl<'ops, 'tcx: 'ops> FunctionCall<'ops, 'tcx> {
    /// The spec of this call: the callee's signature spec instantiated with
    /// the types of the call's arguments and result (see [`spec`]).
    ///
    /// See <https://prusti.github.io/pcg-docs/function-shapes.html> for more info.
    pub(crate) fn shape<'a>(
        self,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>,
    ) -> FunctionShape
    where
        'tcx: 'a,
    {
        let arg_tys: Vec<ty::Ty<'tcx>> = self
            .inputs
            .iter()
            .map(|input| input.ty(ctxt.body(), ctxt.tcx()))
            .collect();
        let callee = if let Some(defined) = self.defined {
            Callee::FnDef(defined.function_data.def_id, defined.caller_substs)
        } else {
            let terminator = ctxt.body()[self.location.block].terminator();
            let mir::TerminatorKind::Call { func, .. } = &terminator.kind else {
                panic!("The call at {:?} is not a call terminator", self.location);
            };
            let func_ty = func.ty(ctxt.body(), ctxt.tcx());
            assert!(
                func_ty.is_fn_ptr(),
                "Unsupported callee type {func_ty:?} at {:?}",
                self.location
            );
            Callee::FnPtr(func_ty.fn_sig(ctxt.tcx()))
        };
        let result_ty = self.output.ty(ctxt).ty;
        let shape = call_spec(&CallSpecQuery {
            callee,
            arg_tys: &arg_tys,
            result_ty,
            env: ctxt.lifetime_env(),
            closure_outlives: &|sup, sub| ctxt.bc().outlives(sup.into(), sub.into(), self.location),
        })
        .unwrap_or_else(|err| panic!("No spec for the call at {:?}: {err:?}", self.location));
        if validity_checks_enabled() {
            check_call_spec(&shape, &arg_tys, result_ty, self.location, ctxt);
        }
        shape
    }
    pub(crate) fn new(
        location: mir::Location,
        inputs: &'ops [&'ops mir::Operand<'tcx>],
        output: utils::Place<'tcx>,
        defined: Option<DefinedFnCall<'tcx>>,
    ) -> Self {
        Self {
            defined,
            location,
            inputs,
            output,
        }
    }
}

pub type FunctionShapeInput<Kind = Generalized> = LifetimeProjection<'static, ArgIdx, Kind>;

impl<Kind: RegionIdxMarker> FunctionShapeInput<Kind> {
    #[must_use]
    pub fn to_function_shape_node(self) -> FunctionShapeNode<Kind> {
        self.with_base(ArgIdxOrResult::Argument(self.base))
    }

    #[must_use]
    pub fn mir_local(self) -> mir::Local {
        self.to_function_shape_node().mir_local()
    }
}

pub type FunctionShapeOutput<Kind = Generalized> =
    LifetimeProjection<'static, ArgIdxOrResult, Kind>;

/// Either an input or output in the shape of the function.
pub type FunctionShapeNode<Kind = Generalized> = LifetimeProjection<'static, ArgIdxOrResult, Kind>;

impl<Kind: RegionIdxMarker> From<FunctionShapeInput<Kind>> for FunctionShapeNode<Kind> {
    fn from(value: FunctionShapeInput<Kind>) -> Self {
        value.to_function_shape_node()
    }
}

impl<Kind: RegionIdxMarker> FunctionShapeNode<Kind> {
    #[must_use]
    pub fn mir_local(self) -> mir::Local {
        match self.base {
            ArgIdxOrResult::Argument(arg) => (*arg + 1).into(),
            ArgIdxOrResult::Result => mir::RETURN_PLACE,
        }
    }

    #[must_use]
    pub fn ty(self, sig: ty::FnSig<'_>) -> ty::Ty<'_> {
        match self.base {
            ArgIdxOrResult::Argument(arg) => sig.inputs()[*arg],
            ArgIdxOrResult::Result => sig.output(),
        }
    }
}

/// A bipartite graph describing the shape of a function. Note that *outputs*
/// include lifetime projections of nested lifetimes in the function arguments.
///
/// The `Kind` parameter distinguishes between shapes built from lifetime
/// projections ([`Region`], the default, used for call shapes) and generalized
/// lifetime projections ([`Generalized`], used for signature shapes).
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct FunctionShape<Kind: RegionIdxMarker = Generalized> {
    inputs: Vec<FunctionShapeInput<Kind>>,
    outputs: Vec<FunctionShapeOutput<Kind>>,
    edges: BTreeSet<
        AbstractionBlockEdge<'static, FunctionShapeInput<Kind>, FunctionShapeOutput<Kind>>,
    >,
}

impl<Kind: RegionIdxMarker> FunctionShape<Kind> {
    pub fn edges(
        &self,
    ) -> impl Iterator<
        Item = AbstractionBlockEdge<'static, FunctionShapeInput<Kind>, FunctionShapeOutput<Kind>>,
    > + '_ {
        self.edges.iter().copied()
    }

    #[must_use]
    pub fn take_inputs_and_outputs(
        self,
    ) -> (
        Vec<FunctionShapeInput<Kind>>,
        Vec<FunctionShapeOutput<Kind>>,
    ) {
        (self.inputs, self.outputs)
    }

    /// Constructs a `FunctionShape` from explicit inputs, outputs, and edges.
    #[must_use]
    pub fn from_raw(
        inputs: Vec<(ArgIdx, usize)>,
        outputs: Vec<(ArgIdxOrResult, usize)>,
        edges: HashSet<((ArgIdx, usize), (ArgIdxOrResult, usize))>,
    ) -> Self {
        let inputs = inputs
            .into_iter()
            .map(|(base, region)| FunctionShapeInput::from_index(base, region.into()))
            .collect();
        let outputs = outputs
            .into_iter()
            .map(|(base, region)| FunctionShapeOutput::from_index(base, region.into()))
            .collect();
        let edges = edges
            .into_iter()
            .map(|((in_base, in_region), (out_base, out_region))| {
                AbstractionBlockEdge::new(
                    FunctionShapeInput::from_index(in_base, in_region.into()),
                    FunctionShapeOutput::from_index(out_base, out_region.into()),
                )
            })
            .collect();
        Self {
            inputs,
            outputs,
            edges,
        }
    }
}

impl FunctionShape {
    /// The spec of the call to `call` at `location`: the callee's signature
    /// spec instantiated with the call's types (see [`spec`]).
    pub fn for_fn_call<'a, 'tcx: 'a>(
        call: DefinedFnCallWithCallTys<'tcx>,
        location: mir::Location,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx> + Copy,
    ) -> Result<Self, MakeFunctionShapeError> {
        let DefinedFnCallWithCallTys {
            defined_fn_call,
            call_arg_tys,
            call_result_ty,
        } = call;
        call_spec(&CallSpecQuery {
            callee: Callee::FnDef(
                defined_fn_call.function_data.def_id,
                defined_fn_call.caller_substs,
            ),
            arg_tys: &call_arg_tys,
            result_ty: call_result_ty,
            env: ctxt.lifetime_env(),
            closure_outlives: &|sup, sub| ctxt.bc().outlives(sup.into(), sub.into(), location),
        })
    }

    /// The spec of the function `def_id` for its own body: its signature
    /// spec with its own generic parameters.
    pub fn for_fn_sig<'tcx, Ctxt: HasTyCtxt<'tcx> + Copy>(
        def_id: DefId,
        ctxt: Ctxt,
    ) -> Result<Self, MakeFunctionShapeError> {
        FunctionData::new(def_id).shape(ctxt)
    }
}

#[derive(Copy, PartialEq, Eq, Clone, Debug, Hash)]
pub struct FunctionData<'tcx> {
    pub(crate) def_id: DefId,
    _marker: PhantomData<&'tcx ()>,
}

impl<'tcx, Ctxt: HasTyCtxt<'tcx>> DisplayWithCtxt<Ctxt> for FunctionData<'tcx> {
    fn display_output(&self, ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        ctxt.tcx().def_path_str(self.def_id).into()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MakeFunctionShapeError {
    ContainsAliasType,
    UnsupportedRustVersion,
    NoFunctionData,
}

impl<'tcx> FunctionData<'tcx> {
    #[must_use]
    pub fn new(def_id: DefId) -> Self {
        Self {
            def_id,
            _marker: PhantomData,
        }
    }

    #[must_use]
    pub fn identity_substs(self, tcx: ty::TyCtxt<'tcx>) -> GenericArgsRef<'tcx> {
        ty::GenericArgs::identity_for_item(tcx, self.def_id)
    }

    #[must_use]
    pub fn param_env(self, tcx: ty::TyCtxt<'tcx>) -> ty::ParamEnv<'tcx> {
        tcx.param_env(self.def_id)
    }

    #[must_use]
    pub fn def_id(self) -> DefId {
        self.def_id
    }

    /// The spec of this function for its own body: the flows between the
    /// lifetime projections of its identity signature, in its own
    /// environment. Its nodes are the lifetime projections of the body's
    /// arguments and result.
    ///
    /// A closure's spec computed here lacks the relations that the closure
    /// body needs between its captures and its signature (see
    /// [`CallSpecQuery::closure_outlives`]): they are known only to the
    /// borrow checker of the closure's body.
    pub fn shape<Ctxt: HasTyCtxt<'tcx> + Copy>(
        self,
        ctxt: Ctxt,
    ) -> Result<FunctionShape<Generalized>, MakeFunctionShapeError> {
        let tcx = ctxt.tcx();
        let sig = self.identity_fn_sig(tcx);
        call_spec(&CallSpecQuery {
            callee: Callee::FnDef(self.def_id, self.identity_substs(tcx)),
            arg_tys: sig.inputs(),
            result_ty: sig.output(),
            env: LifetimeEnv::new(tcx, self.def_id),
            closure_outlives: &|_, _| false,
        })
    }

    pub fn coupled_edges(
        self,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Result<FunctionShapeCoupledEdges<Generalized>, CoupleAbstractionError> {
        Ok(self.shape(tcx)?.coupled_edges())
    }
}

impl std::fmt::Display for ArgIdx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "a{}", self.0)
    }
}

impl std::fmt::Display for ArgIdxOrResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ArgIdxOrResult::Argument(arg) => write!(f, "{arg}"),
            ArgIdxOrResult::Result => write!(f, "result"),
        }
    }
}
impl<Kind: RegionIdxMarker, Ctxt: Copy> DisplayWithCtxt<Ctxt> for FunctionShape<Kind>
where
    FunctionShapeInput<Kind>: DisplayWithCtxt<Ctxt>,
    FunctionShapeOutput<Kind>: DisplayWithCtxt<Ctxt>,
    AbstractionBlockEdge<'static, FunctionShapeInput<Kind>, FunctionShapeOutput<Kind>>:
        DisplayWithCtxt<Ctxt>,
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Seq(vec![
            "Inputs: ".into(),
            self.inputs.display_output(ctxt, mode),
            "\nOutputs: ".into(),
            self.outputs.display_output(ctxt, mode),
            "\nEdges: ".into(),
            self.edges().collect::<Vec<_>>().display_output(ctxt, mode),
        ])
    }
}

impl<Kind: RegionIdxMarker> std::fmt::Display for FunctionShape<Kind> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn fmt_input<K: RegionIdxMarker>(
            f: &mut std::fmt::Formatter<'_>,
            input: &FunctionShapeInput<K>,
        ) -> std::fmt::Result {
            write!(f, "Arg({})↓{}", *input.base, input.region_idx.index())
        }

        fn fmt_output<K: RegionIdxMarker>(
            f: &mut std::fmt::Formatter<'_>,
            output: &FunctionShapeOutput<K>,
        ) -> std::fmt::Result {
            match output.base {
                ArgIdxOrResult::Argument(arg) => {
                    write!(f, "Arg({})↓{}", *arg, output.region_idx.index())
                }
                ArgIdxOrResult::Result => {
                    write!(f, "Result↓{}", output.region_idx.index())
                }
            }
        }

        write!(f, "Inputs: [")?;
        for (i, input) in self.inputs.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            fmt_input(f, input)?;
        }
        write!(f, "]\nOutputs: [")?;
        for (i, output) in self.outputs.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            fmt_output(f, output)?;
        }
        write!(f, "]\nEdges: [")?;
        for (i, edge) in self.edges.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            fmt_input(f, &edge.input)?;
            write!(f, " -> ")?;
            fmt_output(f, &edge.output)?;
        }
        write!(f, "]")
    }
}

impl<Kind: RegionIdxMarker> FunctionShape<Kind> {
    #[allow(unused)]
    pub(crate) fn is_specialization_of(&self, other: &Self) -> bool {
        self.edges.is_subset(&other.edges)
    }

    #[must_use]
    pub fn coupled_edges(&self) -> FunctionShapeCoupledEdges<Kind> {
        CoupledEdgesData::new(self.edges.iter().copied())
    }
}

pub type FunctionShapeCoupledEdges<Kind = Generalized> =
    CoupledEdgesData<FunctionShapeInput<Kind>, FunctionShapeOutput<Kind>>;

#[cfg(test)]
mod tests {
    use crate::{
        borrow_pcg::region_projection::{
            ExtractRegionsCtxt, LifetimeProjectionIdx, PcgRegion, Region,
        },
        rustc_interface::index::IndexVec,
    };

    use super::*;

    #[test]
    fn test_max_function_shape() {
        // fn max<'a>(rx: &'a mut i32, ry: &'a mut i32) -> &'a mut i32

        let tick_a: PcgRegion = PcgRegion::RegionVid(0u32.into());
        #[derive(Clone, Copy)]
        struct TestCtxt(PcgRegion<'static>);

        impl ExtractRegionsCtxt<'static, ArgIdx, PcgRegion<'static>> for TestCtxt {
            fn extract_regions(
                self,
                _data: ArgIdx,
            ) -> IndexVec<LifetimeProjectionIdx<Region>, PcgRegion<'static>> {
                IndexVec::from_raw(vec![self.0])
            }
        }

        impl ExtractRegionsCtxt<'static, ArgIdxOrResult, PcgRegion<'static>> for TestCtxt {
            fn extract_regions(
                self,
                _data: ArgIdxOrResult,
            ) -> IndexVec<LifetimeProjectionIdx<Region>, PcgRegion<'static>> {
                IndexVec::from_raw(vec![self.0])
            }
        }

        impl DisplayWithCtxt<TestCtxt> for PcgRegion<'_> {
            fn display_output(&self, _ctxt: TestCtxt, _mode: OutputMode) -> DisplayOutput {
                format!("{self:?}").into()
            }
        }

        let rx = FunctionShapeInput::new(0.into(), tick_a, None, TestCtxt(tick_a)).unwrap();
        let ry = FunctionShapeInput::new(1.into(), tick_a, None, TestCtxt(tick_a)).unwrap();
        let result =
            FunctionShapeOutput::new(ArgIdxOrResult::Result, tick_a, None, TestCtxt(tick_a))
                .unwrap();
        let shape = FunctionShape {
            inputs: vec![rx, ry],
            outputs: vec![result],
            edges: BTreeSet::from([
                AbstractionBlockEdge::new(rx, result),
                AbstractionBlockEdge::new(ry, result),
            ]),
        };
        let coupled_edges = shape.coupled_edges();
        assert_eq!(coupled_edges.len(), 1);
        let edge = &coupled_edges.0[0];
        assert_eq!(edge.inputs(), &[rx, ry]);
        assert_eq!(edge.outputs(), &[result]);
    }
}
