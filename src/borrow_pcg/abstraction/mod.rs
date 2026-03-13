use std::{collections::BTreeSet, marker::PhantomData};

use derive_more::{Deref, From};

use crate::{
    borrow_pcg::{
        edge::abstraction::{
            AbstractionBlockEdge,
            function::{
                CallDatatypes, DefinedFnCallShapeDataSource, DefinedFnTarget, FunctionCallData,
                FunctionDefShapeDataSource, RustCallDatatypes,
            },
        },
        region_projection::{
            HasTy, LifetimeProjection, OverrideRegionDebugString, PcgRegion, RegionIdx,
        },
        visitor::extract_regions,
    },
    coupling::{CoupleAbstractionError, CoupledEdgesData},
    rustc_interface::{
        middle::{
            mir,
            ty::{self, GenericArgsRef},
        },
        span::def_id::DefId,
    },
    utils::{
        self, CompilerCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, HasTyCtxt,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
    },
};

#[derive(Deref, From, Copy, Clone, Debug, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct ArgIdx(usize);

impl crate::Sealed for ArgIdx {}

impl<'tcx, Ctxt: HasTyCtxt<'tcx>>
    HasTy<'tcx, (FunctionData<'tcx>, Option<GenericArgsRef<'tcx>>, Ctxt)> for ArgIdx
{
    fn rust_ty(
        &self,
        (function_data, substs, ctxt): (FunctionData<'tcx>, Option<GenericArgsRef<'tcx>>, Ctxt),
    ) -> ty::Ty<'tcx> {
        function_data.fn_sig(substs, ctxt.tcx()).inputs()[self.0]
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

impl<T, U, V: OverrideRegionDebugString> OverrideRegionDebugString for (T, U, V) {
    fn override_region_debug_string(&self, region: ty::RegionVid) -> Option<&str> {
        self.2.override_region_debug_string(region)
    }
}

impl<'tcx, Ctxt: HasTyCtxt<'tcx>>
    HasTy<'tcx, (FunctionData<'tcx>, Option<GenericArgsRef<'tcx>>, Ctxt)> for ArgIdxOrResult
{
    fn rust_ty(
        &self,
        (function_data, substs, ctxt): (FunctionData<'tcx>, Option<GenericArgsRef<'tcx>>, Ctxt),
    ) -> ty::Ty<'tcx> {
        match self {
            ArgIdxOrResult::Argument(arg) => arg.rust_ty((function_data, substs, ctxt.tcx())),
            ArgIdxOrResult::Result => function_data.fn_sig(substs, ctxt.tcx()).output(),
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckOutlivesError<'tcx> {
    CannotCompareRegions {
        sup: PcgRegion<'tcx>,
        sub: PcgRegion<'tcx>,
        loc: mir::Location,
    },
}

pub(crate) trait CallShapeDataSource<'tcx, Ctxt> {
    fn location(&self) -> mir::Location;
    fn target(&self) -> Option<DefinedFnTarget<'tcx>>;
    fn call_input_tys(&self, ctxt: Ctxt) -> Vec<ty::Ty<'tcx>>;
    fn call_output_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx>;

    fn call_region_outlives(
        &self,
        sup: PcgRegion<'tcx>,
        sub: PcgRegion<'tcx>,
        ctxt: Ctxt,
    ) -> Result<bool, CheckOutlivesError<'tcx>>;
}

pub(crate) trait FnShapeDataSource<'tcx, Ctxt> {
    fn fn_sig(&self, ctxt: Ctxt) -> ty::FnSig<'tcx>;
    fn fn_region_outlives(
        &self,
        sup: PcgRegion<'tcx>,
        sub: PcgRegion<'tcx>,
        ctxt: Ctxt,
    ) -> Result<bool, CheckOutlivesError<'tcx>>;

    fn fn_input_tys(&self, ctxt: Ctxt) -> Vec<ty::Ty<'tcx>> {
        self.fn_sig(ctxt).inputs().iter().copied().collect()
    }

    fn fn_output_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx> {
        self.fn_sig(ctxt).output()
    }
}

impl<'operands, 'a, 'tcx: 'a + 'operands, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx> + Copy>
    CallShapeDataSource<'tcx, Ctxt> for FunctionCallData<'tcx, RustCallDatatypes<'operands>>
{
    fn call_input_tys(&self, ctxt: Ctxt) -> Vec<ty::Ty<'tcx>> {
        self.inputs
            .iter()
            .map(|input| input.ty(ctxt.body(), ctxt.tcx()))
            .collect()
    }

    fn call_output_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx> {
        self.output_place.ty(ctxt).ty
    }

    fn call_region_outlives(
        &self,
        sup: PcgRegion<'tcx>,
        sub: PcgRegion<'tcx>,
        ctxt: Ctxt,
    ) -> Result<bool, CheckOutlivesError<'tcx>> {
        Ok(ctxt.bc().outlives(sup, sub, self.location))
    }

    fn location(&self) -> mir::Location {
        self.location
    }

    fn target(&self) -> Option<DefinedFnTarget<'tcx>> {
        self.target
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
    fn with_base<U>(self, base: U) -> ProjectionData<'tcx, U> {
        ProjectionData {
            base,
            ty: self.ty,
            region_idx: self.region_idx,
            region: self.region,
        }
    }

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

    pub fn for_fn<'tcx>(def_id: DefId, tcx: ty::TyCtxt<'tcx>) -> Result<FunctionShape, MakeFunctionShapeError<'tcx>> {
        FunctionDefShapeDataSource::new(def_id, tcx).shape(tcx)
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

    pub fn shape(
        self,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Result<FunctionShape, MakeFunctionShapeError<'tcx>> {
        FunctionDefShapeDataSource::new(self.def_id, tcx).shape(tcx)
    }

    pub fn coupled_edges(
        self,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Result<FunctionShapeCoupledEdges, CoupleAbstractionError<'tcx>> {
        let shape = self
            .shape(tcx)
            .map_err(CoupleAbstractionError::MakeFunctionShape)?;
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

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub(crate) struct ForCall;
#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub(crate) struct ForFn;

pub(crate) trait FunctionShapeDataSource<'tcx, Usage, Ctxt: HasTyCtxt<'tcx> + Copy> {
    fn shape_input_tys(&self, ctxt: Ctxt) -> Vec<ty::Ty<'tcx>>;
    fn shape_output_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx>;

    /// Checks whether `sup` outlives `sub` in the context of this shape.
    fn region_outlives(
        &self,
        sup: PcgRegion<'tcx>,
        sub: PcgRegion<'tcx>,
        ctxt: Ctxt,
    ) -> Result<bool, CheckOutlivesError<'tcx>>;

    fn input_projections(&self, ctxt: Ctxt) -> Vec<ProjectionData<'tcx, ArgIdx>> {
        self.shape_input_tys(ctxt)
            .into_iter()
            .enumerate()
            .flat_map(|(arg_idx, ty)| ProjectionData::nodes_for_ty(ArgIdx(arg_idx), ty))
            .collect()
    }

    fn result_projections(&self, ctxt: Ctxt) -> Vec<ProjectionData<'tcx, ArgIdxOrResult>> {
        ProjectionData::nodes_for_ty(ArgIdxOrResult::Result, self.shape_output_ty(ctxt))
    }

    fn output_projections(&self, ctxt: Ctxt) -> Vec<ProjectionData<'tcx, ArgIdxOrResult>> {
        let mut inputs = self
            .input_projections(ctxt)
            .into_iter()
            .flat_map(|input| {
                if ctxt.region_is_invariant_in_type(input.region, input.ty) {
                    Some(input.with_base(ArgIdxOrResult::Argument(input.base)))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        let outputs = self
            .result_projections(ctxt)
            .into_iter()
            .map(|output| output.with_base(ArgIdxOrResult::Result));
        inputs.extend(outputs);
        inputs
    }

    fn shape(&self, ctxt: Ctxt) -> Result<FunctionShape, MakeFunctionShapeError<'tcx>> {
        let inputs = self.input_projections(ctxt);
        let outputs = self.output_projections(ctxt);
        let mut edges = BTreeSet::default();
        for input in inputs.iter() {
            for output in outputs.iter() {
                let should_connect = self
                    .region_outlives(input.region, output.region, ctxt)
                    .map_err(MakeFunctionShapeError::CheckOutlivesError)?;
                if should_connect {
                    edges.insert(AbstractionBlockEdge::new((*input).into(), (*output).into()));
                }
            }
        }
        Ok(FunctionShape {
            inputs: inputs.into_iter().map(|input| input.into()).collect(),
            outputs: outputs.into_iter().map(|output| output.into()).collect(),
            edges,
        })
    }
}

impl FunctionShape {
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
