use derive_more::{Deref, From};
use itertools::Itertools;

use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        region_projection::{LifetimeProjection, PcgRegion, RegionIdx},
        visitor::extract_regions,
    },
    rustc_interface::middle::{mir, ty},
    utils::{
        self, CompilerCtxt, HasBorrowCheckerCtxt, data_structures::HashSet,
        display::DisplayWithCompilerCtxt,
    },
};

#[derive(Deref, From, Copy, Clone, Debug, Hash, Eq, PartialEq)]
pub struct ArgIdx(usize);

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq)]
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

pub(crate) trait FunctionShapeDataSource<'tcx> {
    fn input_tys(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Vec<ty::Ty<'tcx>>;
    fn output_ty(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> ty::Ty<'tcx>;
    fn outlives(&self, sup: PcgRegion, sub: PcgRegion, ctxt: CompilerCtxt<'_, 'tcx>) -> bool;
}

impl<'tcx> FunctionShapeDataSource<'tcx> for FunctionCall<'_, 'tcx> {
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
    for LifetimeProjection<'tcx, T>
{
    fn from(data: ProjectionData<'tcx, T>) -> Self {
        LifetimeProjection::from_index(data.base, data.region_idx)
    }
}

impl<'tcx> From<ProjectionData<'tcx, ArgIdx>> for LifetimeProjection<'tcx, ArgIdxOrResult> {
    fn from(data: ProjectionData<'tcx, ArgIdx>) -> Self {
        LifetimeProjection::from_index(ArgIdxOrResult::Argument(data.base), data.region_idx)
    }
}

#[derive(Deref, PartialEq, Eq, Clone, Debug)]
pub struct FunctionShape<'tcx>(
    HashSet<(
        LifetimeProjection<'tcx, ArgIdx>,
        LifetimeProjection<'tcx, ArgIdxOrResult>,
    )>,
);

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

impl<'tcx> DisplayWithCompilerCtxt<'tcx, &dyn BorrowCheckerInterface<'tcx>>
    for FunctionShape<'tcx>
{
    fn to_short_string(&self, _ctxt: CompilerCtxt<'_, 'tcx>) -> String {
        self.0
            .iter()
            .map(|(input, output)| format!("{input} -> {output}"))
            .sorted()
            .collect::<Vec<_>>()
            .join("\n, ")
    }
}

impl<'a, 'tcx: 'a> FunctionShape<'tcx> {
    #[allow(unused)]
    pub(crate) fn is_specialization_of(&self, other: &Self) -> bool {
        self.0.is_subset(&other.0)
    }

    #[allow(unused)]
    pub(crate) fn diff(&self, other: &Self) -> Self {
        let diff = self.0.difference(&other.0).copied().collect::<HashSet<_>>();
        Self(diff)
    }

    pub(crate) fn new<ShapeData: FunctionShapeDataSource<'tcx>>(
        shape_data: &ShapeData,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> Self {
        let mut shape = HashSet::default();
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
                if ctxt
                    .bc_ctxt()
                    .region_is_invariant_in_type(output.region, output.ty)
                    && shape_data.outlives(input.region, output.region, ctxt)
                {
                    tracing::debug!("{} outlives {}", input, output);
                    shape.insert((input.into(), output.into()));
                }
            }
            for rp in result_projections.iter().copied() {
                if shape_data.outlives(input.region, rp.region, ctxt) {
                    tracing::debug!("{} outlives {}", input, rp);
                    shape.insert((input.into(), rp.into()));
                }
            }
        }

        FunctionShape(shape)
    }
}
