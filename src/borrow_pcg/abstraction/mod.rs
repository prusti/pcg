use std::collections::BTreeSet;

use derive_more::{Deref, From};
use itertools::Itertools;

use crate::{
    borrow_pcg::{
        edge::abstraction::{AbstractionBlockEdge, function::FunctionDataShapeDataSource},
        region_projection::{LifetimeProjection, PcgRegion, RegionIdx},
        visitor::extract_regions,
    },
    coupling::CoupleAbstractionError,
    rustc_interface::{
        middle::{
            mir,
            ty::{self, GenericArgsRef},
        },
        span::def_id::{DefId, LocalDefId},
    },
    utils::{self, CompilerCtxt, HasTyCtxt, display::{DisplayOutput, DisplayWithCtxt}},
};

use crate::coupling::{CoupleInputError, CoupledEdgesData};

#[derive(Deref, From, Copy, Clone, Debug, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct ArgIdx(usize);

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum ArgIdxOrResult {
    Argument(ArgIdx),
    Result,
}

pub(crate) struct FunctionCall<'a, 'tcx> {
    pub(crate) location: mir::Location,
    pub(crate) inputs: &'a [&'a mir::Operand<'tcx>],
    pub(crate) output: utils::Place<'tcx>,
}

impl<'a, 'tcx> FunctionCall<'a, 'tcx> {
    pub(crate) fn new(
        location: mir::Location,
        inputs: &'a [&'a mir::Operand<'tcx>],
        output: utils::Place<'tcx>,
    ) -> Self {
        Self {
            location,
            inputs,
            output,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckOutlivesError {
    CannotCompareRegions { sup: PcgRegion, sub: PcgRegion },
}

pub(crate) trait FunctionShapeDataSource<'tcx> {
    type Ctxt: HasTyCtxt<'tcx> + Copy;
    fn input_tys(&self, ctxt: Self::Ctxt) -> Vec<ty::Ty<'tcx>>;
    fn output_ty(&self, ctxt: Self::Ctxt) -> ty::Ty<'tcx>;
    fn outlives(
        &self,
        sup: PcgRegion,
        sub: PcgRegion,
        ctxt: Self::Ctxt,
    ) -> Result<bool, CheckOutlivesError>;

    fn input_arg_projections(&self, ctxt: Self::Ctxt) -> Vec<ProjectionData<'tcx, ArgIdx>> {
        self.input_tys(ctxt)
            .into_iter()
            .enumerate()
            .flat_map(|(i, ty)| ProjectionData::nodes_for_ty(i.into(), ty))
            .collect()
    }

    fn result_projections(&self, ctxt: Self::Ctxt) -> Vec<ProjectionData<'tcx, ArgIdxOrResult>> {
        ProjectionData::nodes_for_ty(ArgIdxOrResult::Result, self.output_ty(ctxt))
    }

    fn inputs(&self, ctxt: Self::Ctxt) -> Vec<FunctionShapeInput> {
        self.input_arg_projections(ctxt)
            .into_iter()
            .map(|p| p.into())
            .collect()
    }

    fn outputs(&self, ctxt: Self::Ctxt) -> Vec<FunctionShapeOutput> {
        self.result_projections(ctxt)
            .into_iter()
            .map(|p| p.into())
            .collect()
    }
}

impl<'a, 'tcx> FunctionShapeDataSource<'tcx> for FunctionCall<'a, 'tcx> {
    type Ctxt = CompilerCtxt<'a, 'tcx>;
    fn input_tys(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Vec<ty::Ty<'tcx>> {
        self.inputs
            .iter()
            .map(|input| input.ty(ctxt.body(), ctxt.tcx()))
            .collect()
    }

    fn output_ty(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> ty::Ty<'tcx> {
        self.output.ty(ctxt).ty
    }

    fn outlives(
        &self,
        sup: PcgRegion,
        sub: PcgRegion,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, CheckOutlivesError> {
        Ok(ctxt.bc.outlives(sup, sub, self.location))
    }
}

#[derive(Copy, PartialEq, Eq, Clone, Debug, Hash)]
pub(crate) struct ProjectionData<'tcx, T> {
    base: T,
    ty: ty::Ty<'tcx>,
    region_idx: RegionIdx,
    region: PcgRegion,
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
    pub fn to_function_shape_node(self) -> FunctionShapeNode {
        self.with_base(ArgIdxOrResult::Argument(self.base))
    }

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
    pub fn mir_local(self) -> mir::Local {
        match self.base {
            ArgIdxOrResult::Argument(arg) => (*arg + 1).into(),
            ArgIdxOrResult::Result => mir::RETURN_PLACE,
        }
    }

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

    pub fn take_inputs_and_outputs(self) -> (Vec<FunctionShapeInput>, Vec<FunctionShapeOutput>) {
        (self.inputs, self.outputs)
    }

    pub fn for_fn<'tcx>(
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        caller_def_id: Option<LocalDefId>,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Result<Self, MakeFunctionShapeError> {
        let data = FunctionData::new(def_id, substs, caller_def_id);
        Self::new(&data.shape_data_source(tcx)?, tcx)
            .map_err(MakeFunctionShapeError::CheckOutlivesError)
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub struct FunctionData<'tcx> {
    pub(crate) def_id: DefId,
    pub(crate) substs: GenericArgsRef<'tcx>,
    pub(crate) caller_def_id: Option<LocalDefId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MakeFunctionShapeError {
    ContainsAliasType,
    UnsupportedRustVersion,
    NoFunctionData,
    CheckOutlivesError(CheckOutlivesError),
}

impl<'tcx> FunctionData<'tcx> {
    pub fn new(
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        caller_def_id: Option<LocalDefId>,
    ) -> Self {
        Self {
            def_id,
            substs,
            caller_def_id,
        }
    }

    pub fn param_env(self, tcx: ty::TyCtxt<'tcx>) -> ty::ParamEnv<'tcx> {
        let def_id = self
            .caller_def_id
            .map(|local_def_id| local_def_id.to_def_id())
            .unwrap_or(self.def_id);
        tcx.param_env(def_id)
    }

    pub fn substs(self) -> GenericArgsRef<'tcx> {
        self.substs
    }

    pub fn def_id(self) -> DefId {
        self.def_id
    }

    pub(crate) fn shape_data_source(
        self,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Result<FunctionDataShapeDataSource<'tcx>, MakeFunctionShapeError> {
        FunctionDataShapeDataSource::new(self, tcx)
    }

    pub fn shape(self, tcx: ty::TyCtxt<'tcx>) -> Result<FunctionShape, MakeFunctionShapeError> {
        FunctionShape::new(&self.shape_data_source(tcx)?, tcx)
            .map_err(MakeFunctionShapeError::CheckOutlivesError)
    }

    pub fn coupled_edges(
        self,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Result<FunctionShapeCoupledEdges, CoupleAbstractionError> {
        let shape = self
            .shape(tcx)
            .map_err(CoupleAbstractionError::MakeFunctionShape)?;
        shape
            .coupled_edges()
            .map_err(CoupleAbstractionError::CoupleInput)
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

impl<Ctxt> DisplayWithCtxt<Ctxt> for FunctionShape {
    fn output(&self, _ctxt: Ctxt) -> DisplayOutput {
        DisplayOutput::Text(
            self.edges
                .iter()
                .map(|edge| format!("{edge}"))
                .sorted()
                .collect::<Vec<_>>()
                .join("\n, ")
        )
    }
}

impl FunctionShape {
    #[allow(unused)]
    pub(crate) fn is_specialization_of(&self, other: &Self) -> bool {
        self.edges.is_subset(&other.edges)
    }

    pub(crate) fn new<'tcx, ShapeData: FunctionShapeDataSource<'tcx>>(
        shape_data: &ShapeData,
        ctxt: ShapeData::Ctxt,
    ) -> Result<Self, CheckOutlivesError> {
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

    pub fn coupled_edges(
        &self,
    ) -> std::result::Result<FunctionShapeCoupledEdges, CoupleInputError> {
        CoupledEdgesData::new(self.edges.iter().copied())
    }
}

pub type FunctionShapeCoupledEdges = CoupledEdgesData<FunctionShapeInput, FunctionShapeOutput>;
