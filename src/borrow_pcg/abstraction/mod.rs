use std::{
    collections::{BTreeSet, HashSet},
    marker::PhantomData,
};

use derive_more::{Deref, From};

use crate::{
    HasSettings,
    borrow_pcg::{
        edge::abstraction::{
            AbstractionBlockEdge,
            function::{
                DefinedFnCall, DefinedFnCallShapeDataSource, DefinedFnSigShapeDataSource,
                FnCallDataSource,
            },
        },
        region_projection::{
            HasTy, LifetimeProjection, OverrideRegionDebugString, PcgRegion, RegionIdx,
        },
        visitor::extract_regions,
    },
    coupling::{CoupleAbstractionError, CoupledEdgesData},
    pcg_validity_assert,
    rustc_interface::{
        index::Idx,
        middle::{
            mir,
            ty::{self, GenericArgsRef},
        },
        span::def_id::DefId,
    },
    utils::{
        self, CompilerCtxt, HasBorrowCheckerCtxt, HasTyCtxt,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
    },
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
        format!("{self}").into()
    }
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum ArgIdxOrResult {
    Argument(ArgIdx),
    Result,
}

impl crate::Sealed for ArgIdxOrResult {}

impl<'tcx> OverrideRegionDebugString for (FunctionData<'tcx>, ty::TyCtxt<'tcx>) {
    fn override_region_debug_string(&self, _region: ty::RegionVid) -> Option<&str> {
        None
    }
}

impl<T, U: OverrideRegionDebugString> OverrideRegionDebugString for (T, U) {
    fn override_region_debug_string(&self, region: ty::RegionVid) -> Option<&str> {
        self.1.override_region_debug_string(region)
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
    /// Computes the shape for this function call. For defined function calls,
    /// uses the sig-derived call shape: computes the signature shape using the
    /// instantiated signature types, then remaps region indices to the
    /// call-site types (handling unnormalized alias types in the sig).
    pub(crate) fn shape<'a>(
        self,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>,
    ) -> FunctionShape
    where
        'tcx: 'a,
    {
        match self.defined {
            Some(defined) => {
                let data_source = DefinedFnCallShapeDataSource::new(defined, ctxt.tcx()).unwrap();
                let sig_shape = FunctionShape::new(&data_source, ctxt).unwrap();
                let call_input_tys: Vec<_> = self
                    .inputs
                    .iter()
                    .map(|input| input.ty(ctxt.body(), ctxt.tcx()))
                    .collect();
                let call_output_ty = self.output.ty(ctxt).ty;
                let sig_input_tys = data_source.input_tys(ctxt);
                let sig_output_ty = data_source.output_ty(ctxt);
                sig_shape.remap_to_call_site(
                    &call_input_tys,
                    call_output_ty,
                    &sig_input_tys,
                    sig_output_ty,
                    ctxt,
                )
            }
            None => FunctionShape::new(
                &FnCallDataSource::new(
                    self.location,
                    self.inputs
                        .iter()
                        .map(|input| input.ty(ctxt.body(), ctxt.tcx()))
                        .collect(),
                    self.output.ty(ctxt).ty,
                ),
                ctxt,
            )
            .unwrap(),
        }
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckOutlivesError<'tcx> {
    CannotCompareRegions {
        sup: PcgRegion<'tcx>,
        sub: PcgRegion<'tcx>,
    },
}

pub(crate) trait FunctionShapeDataSource<'tcx, Ctxt> {
    fn input_tys(&self, ctxt: Ctxt) -> Vec<ty::Ty<'tcx>>;
    fn output_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx>;
    fn outlives(
        &self,
        sup: PcgRegion<'tcx>,
        sub: PcgRegion<'tcx>,
        ctxt: Ctxt,
    ) -> Result<bool, CheckOutlivesError<'tcx>>;

    fn input_arg_projections(&self, ctxt: Ctxt) -> Vec<ProjectionData<'tcx, ArgIdx>> {
        self.input_tys(ctxt)
            .into_iter()
            .enumerate()
            .flat_map(|(i, ty)| ProjectionData::nodes_for_ty(i.into(), ty))
            .collect()
    }

    fn result_projections(&self, ctxt: Ctxt) -> Vec<ProjectionData<'tcx, ArgIdxOrResult>> {
        ProjectionData::nodes_for_ty(ArgIdxOrResult::Result, self.output_ty(ctxt))
    }

    fn inputs(&self, ctxt: Ctxt) -> Vec<FunctionShapeInput> {
        self.input_arg_projections(ctxt)
            .into_iter()
            .map(std::convert::Into::into)
            .collect()
    }

    fn outputs(&self, ctxt: Ctxt) -> Vec<FunctionShapeOutput> {
        self.result_projections(ctxt)
            .into_iter()
            .map(std::convert::Into::into)
            .collect()
    }
}

#[derive(Copy, PartialEq, Eq, Clone, Debug, Hash)]
pub(crate) struct ProjectionData<'tcx, T> {
    base: T,
    ty: ty::Ty<'tcx>,
    region_idx: RegionIdx,
    region: PcgRegion<'tcx>,
}

impl<'tcx, T: Copy> ProjectionData<'tcx, T> {
    fn nodes_for_ty(base: T, ty: ty::Ty<'tcx>) -> Vec<Self> {
        extract_regions(ty)
            .into_iter()
            .enumerate()
            .map(|(region_idx, region)| Self {
                base,
                ty,
                region,
                region_idx: region_idx.into(),
            })
            .collect()
    }
}

impl<T: std::fmt::Display> std::fmt::Display for ProjectionData<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({}|{:?}) ({:?}) in type {:?}",
            self.base, self.region_idx, self.region, self.ty
        )
    }
}

impl<'tcx, T: Copy + std::fmt::Debug> From<ProjectionData<'tcx, T>>
    for LifetimeProjection<'static, T>
{
    fn from(data: ProjectionData<'tcx, T>) -> Self {
        LifetimeProjection::from_index(data.base, data.region_idx)
    }
}

impl<'tcx> From<ProjectionData<'tcx, ArgIdx>> for LifetimeProjection<'static, ArgIdxOrResult> {
    fn from(data: ProjectionData<'tcx, ArgIdx>) -> Self {
        LifetimeProjection::from_index(ArgIdxOrResult::Argument(data.base), data.region_idx)
    }
}

pub type FunctionShapeInput = LifetimeProjection<'static, ArgIdx>;

impl FunctionShapeInput {
    #[must_use]
    pub fn to_function_shape_node(self) -> FunctionShapeNode {
        self.with_base(ArgIdxOrResult::Argument(self.base))
    }

    #[must_use]
    pub fn mir_local(self) -> mir::Local {
        self.to_function_shape_node().mir_local()
    }
}

pub type FunctionShapeOutput = LifetimeProjection<'static, ArgIdxOrResult>;

/// Either an input or output in the shape of the function.
pub type FunctionShapeNode = LifetimeProjection<'static, ArgIdxOrResult>;

impl From<FunctionShapeInput> for FunctionShapeNode {
    fn from(value: FunctionShapeInput) -> Self {
        value.to_function_shape_node()
    }
}

impl FunctionShapeNode {
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
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct FunctionShape {
    inputs: Vec<FunctionShapeInput>,
    outputs: Vec<FunctionShapeOutput>,
    edges: BTreeSet<AbstractionBlockEdge<'static, FunctionShapeInput, FunctionShapeOutput>>,
}

impl FunctionShape {
    /// Constructs a `FunctionShape` from explicit inputs, outputs, and edges.
    /// Each input/output/edge endpoint is `(base, region_idx)`.
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

    pub fn edges(
        &self,
    ) -> impl Iterator<Item = AbstractionBlockEdge<'static, FunctionShapeInput, FunctionShapeOutput>>
    {
        self.edges.iter().copied()
    }

    #[must_use]
    pub fn take_inputs_and_outputs(self) -> (Vec<FunctionShapeInput>, Vec<FunctionShapeOutput>) {
        (self.inputs, self.outputs)
    }

    pub fn for_fn<'tcx>(
        def_id: DefId,
        caller_substs: GenericArgsRef<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<Self, MakeFunctionShapeError<'tcx>> {
        let data = FunctionData::new(def_id);
        Self::new(&data.shape_data_source(caller_substs, ctxt.tcx())?, ctxt)
            .map_err(MakeFunctionShapeError::CheckOutlivesError)
    }
}

#[derive(Copy, PartialEq, Eq, Clone, Debug, Hash)]
pub struct FunctionData<'tcx> {
    pub(crate) def_id: DefId,
    _marker: PhantomData<&'tcx ()>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MakeFunctionShapeError<'tcx> {
    ContainsAliasType,
    UnsupportedRustVersion,
    NoFunctionData,
    CheckOutlivesError(CheckOutlivesError<'tcx>),
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

    pub(crate) fn shape_data_source<'a>(
        self,
        caller_substs: GenericArgsRef<'tcx>,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Result<DefinedFnCallShapeDataSource<'a, 'tcx>, MakeFunctionShapeError<'tcx>>
    where
        'tcx: 'a,
    {
        DefinedFnCallShapeDataSource::new(DefinedFnCall::new(self, caller_substs), tcx)
    }

    pub fn shape<'a>(
        self,
        caller_substs: GenericArgsRef<'tcx>,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> Result<FunctionShape, MakeFunctionShapeError<'tcx>> {
        FunctionShape::new(&self.shape_data_source(caller_substs, ctxt.tcx())?, ctxt)
            .map_err(MakeFunctionShapeError::CheckOutlivesError)
    }

    pub fn coupled_edges(
        self,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Result<FunctionShapeCoupledEdges, CoupleAbstractionError<'tcx>> {
        let source = DefinedFnSigShapeDataSource::new(self.def_id, tcx)?;
        let shape =
            FunctionShape::new(&source, tcx).map_err(MakeFunctionShapeError::CheckOutlivesError)?;
        Ok(shape.coupled_edges())
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
impl<Ctxt: Copy> DisplayWithCtxt<Ctxt> for FunctionShape
where
    FunctionShapeInput: DisplayWithCtxt<Ctxt>,
    FunctionShapeOutput: DisplayWithCtxt<Ctxt>,
    AbstractionBlockEdge<'static, FunctionShapeInput, FunctionShapeOutput>: DisplayWithCtxt<Ctxt>,
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

impl FunctionShape {
    #[allow(unused)]
    pub(crate) fn is_specialization_of(&self, other: &Self) -> bool {
        self.edges.is_subset(&other.edges)
    }

    pub(crate) fn new<
        'tcx,
        Ctxt: HasTyCtxt<'tcx> + Copy,
        ShapeData: FunctionShapeDataSource<'tcx, Ctxt>,
    >(
        shape_data: &ShapeData,
        ctxt: Ctxt,
    ) -> Result<Self, CheckOutlivesError<'tcx>> {
        let mut shape: BTreeSet<
            AbstractionBlockEdge<'static, FunctionShapeInput, FunctionShapeOutput>,
        > = BTreeSet::default();
        let arg_projections = shape_data.input_arg_projections(ctxt);
        let result_projections = shape_data.result_projections(ctxt);
        for input in arg_projections.iter().copied() {
            for output in arg_projections.iter().copied() {
                if ctxt.region_is_invariant_in_type(output.region, output.ty)
                    && shape_data.outlives(input.region, output.region, ctxt)?
                {
                    tracing::debug!("{} outlives {}", input, output);
                    shape.insert(AbstractionBlockEdge::new(input.into(), output.into()));
                }
            }
            for rp in result_projections.iter().copied() {
                if shape_data.outlives(input.region, rp.region, ctxt)? {
                    tracing::debug!("{} outlives {}", input, rp);
                    shape.insert(AbstractionBlockEdge::new(input.into(), rp.into()));
                }
            }
        }

        Ok(FunctionShape {
            inputs: shape_data.inputs(ctxt),
            outputs: shape_data.outputs(ctxt),
            edges: shape,
        })
    }

    /// Remaps region indices from signature types to call-site types.
    ///
    /// The signature shape is computed using the instantiated signature, which
    /// may contain unnormalized alias types with extra regions not present in
    /// the call-site types. This method finds the actual region for each sig
    /// shape node and locates its index in the corresponding call-site type,
    /// skipping edges whose regions exist only in the alias type.
    /// Remaps region indices from signature types to call-site types.
    ///
    /// The sig type and call-site type for each argument/result have the same
    /// structure, so the j-th region in the sig type corresponds to the j-th
    /// region in the call-site type. When unnormalized alias types in the sig
    /// introduce extra regions (out of bounds in the call-site type), the
    /// corresponding edges are dropped.
    fn remap_to_call_site<'a, 'tcx: 'a>(
        self,
        call_input_tys: &[ty::Ty<'tcx>],
        call_output_ty: ty::Ty<'tcx>,
        sig_input_tys: &[ty::Ty<'tcx>],
        sig_output_ty: ty::Ty<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>,
    ) -> Self {
        let remap_region_idx = |sig_ty: ty::Ty<'tcx>,
                                call_ty: ty::Ty<'tcx>,
                                sig_region_idx: RegionIdx|
         -> Option<RegionIdx> {
            let call_regions = extract_regions(call_ty);
            if sig_region_idx.index() < call_regions.len() {
                Some(sig_region_idx)
            } else {
                pcg_validity_assert!(
                    false,
                    [ctxt],
                    "remap_to_call_site: dropping sig region idx {:?} (out of bounds for call type {:?} with {} regions, sig type {:?})",
                    sig_region_idx,
                    call_ty,
                    call_regions.len(),
                    sig_ty
                );
                None
            }
        };

        let remap_input = |input: FunctionShapeInput| -> Option<FunctionShapeInput> {
            remap_region_idx(
                sig_input_tys[*input.base],
                call_input_tys[*input.base],
                input.region_idx,
            )?;
            Some(input)
        };

        let remap_output = |output: FunctionShapeOutput| -> Option<FunctionShapeOutput> {
            let (sig_ty, call_ty) = match output.base {
                ArgIdxOrResult::Argument(arg) => (sig_input_tys[*arg], call_input_tys[*arg]),
                ArgIdxOrResult::Result => (sig_output_ty, call_output_ty),
            };
            remap_region_idx(sig_ty, call_ty, output.region_idx)?;
            Some(output)
        };

        let edges = self
            .edges
            .into_iter()
            .filter_map(|edge| {
                let input = remap_input(edge.input)?;
                let output = remap_output(edge.output)?;
                Some(AbstractionBlockEdge::new(input, output))
            })
            .collect();

        let inputs = self.inputs.into_iter().filter_map(remap_input).collect();
        let outputs = self.outputs.into_iter().filter_map(remap_output).collect();

        FunctionShape {
            inputs,
            outputs,
            edges,
        }
    }

    #[must_use]
    pub fn coupled_edges(&self) -> FunctionShapeCoupledEdges {
        CoupledEdgesData::new(self.edges.iter().copied())
    }
}

pub type FunctionShapeCoupledEdges = CoupledEdgesData<FunctionShapeInput, FunctionShapeOutput>;

#[cfg(test)]
mod tests {
    use crate::{borrow_pcg::region_projection::HasRegions, rustc_interface::index::IndexVec};

    use super::*;

    #[test]
    fn test_max_function_shape() {
        // fn max<'a>(rx: &'a mut i32, ry: &'a mut i32) -> &'a mut i32

        let tick_a: PcgRegion = PcgRegion::RegionVid(0u32.into());
        #[derive(Clone, Copy)]
        struct TestCtxt(PcgRegion<'static>);
        impl HasRegions<'static, TestCtxt> for ArgIdx {
            fn regions(&self, ctxt: TestCtxt) -> IndexVec<RegionIdx, PcgRegion<'static>> {
                IndexVec::from_raw(vec![ctxt.0])
            }
        }
        impl HasRegions<'static, TestCtxt> for ArgIdxOrResult {
            fn regions(&self, ctxt: TestCtxt) -> IndexVec<RegionIdx, PcgRegion<'static>> {
                IndexVec::from_raw(vec![ctxt.0])
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
