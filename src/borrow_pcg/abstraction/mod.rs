use std::collections::BTreeSet;

use derive_more::{Deref, From};
use itertools::Itertools;

use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        edge::abstraction::{
            AbstractionBlockEdge,
            function::{FunctionDataShapeDataSource, MakeFunctionShapeError},
        },
        region_projection::{LifetimeProjection, PcgRegion, RegionIdx},
        visitor::extract_regions,
    },
    rustc_interface::{
        middle::{
            mir,
            ty::{self, GenericArgsRef},
        },
        span::def_id::{DefId, LocalDefId},
    },
    utils::{
        self, CompilerCtxt, HasBorrowCheckerCtxt, HasTyCtxt, data_structures::HashSet,
        display::DisplayWithCompilerCtxt,
    },
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

pub trait FunctionShapeDataSource<'tcx> {
    type Ctxt: HasTyCtxt<'tcx> + Copy;
    fn input_tys(&self, ctxt: Self::Ctxt) -> Vec<ty::Ty<'tcx>>;
    fn output_ty(&self, ctxt: Self::Ctxt) -> ty::Ty<'tcx>;
    fn outlives(&self, sup: PcgRegion, sub: PcgRegion, ctxt: Self::Ctxt) -> bool;
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

    fn outlives(&self, sup: PcgRegion, sub: PcgRegion, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        ctxt.bc.outlives(sup, sub, self.location)
    }
}

#[derive(Copy, PartialEq, Eq, Clone, Debug, Hash)]
struct ProjectionData<'tcx, T> {
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
}

pub type FunctionShapeOutput = LifetimeProjection<'static, ArgIdxOrResult>;

pub type FunctionShapeNode = LifetimeProjection<'static, ArgIdxOrResult>;

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

#[derive(Deref, PartialEq, Eq, Clone, Debug, Hash)]
pub struct FunctionShape(
    BTreeSet<AbstractionBlockEdge<'static, FunctionShapeInput, FunctionShapeOutput>>,
);

impl FunctionShape {
    pub fn for_fn<'tcx>(
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        caller_def_id: Option<LocalDefId>,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Result<Self, MakeFunctionShapeError> {
        let data = FunctionData::new(def_id, substs, caller_def_id);
        Ok(Self::new(&data.shape(tcx)?, tcx))
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub struct FunctionData<'tcx> {
    pub(crate) def_id: DefId,
    pub(crate) substs: GenericArgsRef<'tcx>,
    pub(crate) caller_def_id: Option<LocalDefId>,
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
    pub fn shape(
        self,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Result<FunctionDataShapeDataSource<'tcx>, MakeFunctionShapeError> {
        FunctionDataShapeDataSource::new(self, tcx)
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

impl<'tcx> DisplayWithCompilerCtxt<'tcx, &dyn BorrowCheckerInterface<'tcx>> for FunctionShape {
    fn to_short_string(&self, _ctxt: CompilerCtxt<'_, 'tcx>) -> String {
        self.0
            .iter()
            .map(|edge| format!("{edge}"))
            .sorted()
            .collect::<Vec<_>>()
            .join("\n, ")
    }
}

impl FunctionShape {
    #[allow(unused)]
    pub(crate) fn is_specialization_of(&self, other: &Self) -> bool {
        self.0.is_subset(&other.0)
    }

    #[allow(unused)]
    pub(crate) fn diff(&self, other: &Self) -> Self {
        let diff = self
            .0
            .difference(&other.0)
            .copied()
            .collect::<BTreeSet<_>>();
        Self(diff)
    }

    pub fn new<'tcx, ShapeData: FunctionShapeDataSource<'tcx>>(
        shape_data: &ShapeData,
        ctxt: ShapeData::Ctxt,
    ) -> Self {
        let mut shape: BTreeSet<
            AbstractionBlockEdge<'static, FunctionShapeInput, FunctionShapeOutput>,
        > = BTreeSet::default();
        let input_tys = shape_data.input_tys(ctxt);
        let output_ty = shape_data.output_ty(ctxt);
        let arg_projections = input_tys
            .into_iter()
            .enumerate()
            .flat_map(|(i, ty)| ProjectionData::nodes_for_ty(i.into(), ty))
            .collect::<Vec<ProjectionData<'tcx, ArgIdx>>>();
        let result_projections = ProjectionData::nodes_for_ty(ArgIdxOrResult::Result, output_ty);
        for input in arg_projections.iter().copied() {
            for output in arg_projections.iter().copied() {
                if ctxt.region_is_invariant_in_type(output.region, output.ty)
                    && shape_data.outlives(input.region, output.region, ctxt)
                {
                    tracing::debug!("{} outlives {}", input, output);
                    shape.insert(AbstractionBlockEdge::new(input.into(), output.into()));
                }
            }
            for rp in result_projections.iter().copied() {
                if shape_data.outlives(input.region, rp.region, ctxt) {
                    tracing::debug!("{} outlives {}", input, rp);
                    shape.insert(AbstractionBlockEdge::new(input.into(), rp.into()));
                }
            }
        }

        FunctionShape(shape)
    }

    pub fn coupled(
        &self,
    ) -> std::result::Result<
        CoupledEdgesData<FunctionShapeInput, FunctionShapeOutput>,
        CoupleInputError,
    > {
        CoupledEdgesData::new(self.0.iter().copied())
    }
}
