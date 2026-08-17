//! Interface to the Rust compiler.
pub extern crate rustc_abi as abi;
pub extern crate rustc_ast as ast;
pub extern crate rustc_borrowck as rs_borrowck;
pub extern crate rustc_data_structures as data_structures;
pub extern crate rustc_driver as driver;
pub extern crate rustc_hir as hir;
pub extern crate rustc_index as index;
pub extern crate rustc_infer as infer;
pub extern crate rustc_interface as interface;
pub extern crate rustc_middle as middle;
pub extern crate rustc_mir_dataflow as mir_dataflow;
pub extern crate rustc_session as session;
pub extern crate rustc_span as span;
pub extern crate rustc_target as target;
pub extern crate rustc_trait_selection as trait_selection;

pub mod borrowck;
pub mod dataflow;

#[rustversion::since(2025-03-02)]
mod aliases {
    use crate::rustc_interface::{abi, index, middle};
    pub(crate) type PlaceTy<'tcx> = middle::mir::PlaceTy<'tcx>;
    pub(crate) type FieldIdx = abi::FieldIdx;
    pub(crate) type VariantIdx = abi::VariantIdx;
    pub(crate) type RustBitSet<T> = index::bit_set::DenseBitSet<T>;
}

#[rustversion::before(2025-03-02)]
mod aliases {
    use crate::rustc_interface::{index, middle, target};
    pub(crate) type PlaceTy<'tcx> = middle::mir::tcx::PlaceTy<'tcx>;
    pub(crate) type FieldIdx = target::abi::FieldIdx;
    pub(crate) type VariantIdx = target::abi::VariantIdx;
    pub(crate) type RustBitSet<T> = index::bit_set::BitSet<T>;
}

pub(crate) use aliases::*;

/// `BoundRegion` and `BoundVariableKind` became generic over the interner when
/// `Region` was uplifted from `rustc_middle` into `rustc_type_ir`.
#[rustversion::since(2026-07-21)]
mod bound_var_aliases {
    use crate::rustc_interface::middle::ty;
    pub(crate) type BoundRegion<'tcx> = ty::BoundRegion<'tcx>;
    pub(crate) type BoundVariableKind<'tcx> = ty::BoundVariableKind<'tcx>;
}

#[rustversion::before(2026-07-21)]
mod bound_var_aliases {
    use crate::rustc_interface::middle::ty;
    pub(crate) type BoundRegion<'tcx> = ty::BoundRegion;
    pub(crate) type BoundVariableKind<'tcx> = ty::BoundVariableKind;
}

pub(crate) use bound_var_aliases::*;

/// Discards the `Unnormalized` wrapper that instantiating an `EarlyBinder`
/// introduced, yielding the value the instantiation produced directly before
/// the wrapper existed. PCG does not normalize these types.
#[rustversion::since(2026-04-19)]
pub(crate) fn skip_normalization<T>(value: middle::ty::Unnormalized<'_, T>) -> T {
    value.skip_normalization()
}

#[rustversion::before(2026-04-19)]
pub(crate) fn skip_normalization<T>(value: T) -> T {
    value
}

/// The generic arguments of a `TyKind::FnDef`.
///
/// `FnDef` now holds its arguments behind a binder, as a first step towards
/// late-bound turbofishing. That binder currently binds nothing, so skipping it
/// recovers the arguments as they were before.
#[rustversion::since(2026-07-13)]
pub(crate) fn fn_def_args<'tcx>(
    args: &middle::ty::Binder<'tcx, middle::ty::GenericArgsRef<'tcx>>,
) -> middle::ty::GenericArgsRef<'tcx> {
    args.skip_binder()
}

#[rustversion::before(2026-07-13)]
pub(crate) fn fn_def_args<'tcx>(
    args: &middle::ty::GenericArgsRef<'tcx>,
) -> middle::ty::GenericArgsRef<'tcx> {
    *args
}

/// The type of `field` instantiated with `args`.
///
/// `FieldDef::ty` began returning its result wrapped in `Unnormalized`. PCG uses
/// the instantiated field type without normalizing it, which is what the method
/// returned directly before the wrapper was introduced.
#[rustversion::since(2026-05-13)]
pub(crate) fn field_ty<'tcx>(
    field: &middle::ty::FieldDef,
    tcx: middle::ty::TyCtxt<'tcx>,
    args: middle::ty::GenericArgsRef<'tcx>,
) -> middle::ty::Ty<'tcx> {
    field.ty(tcx, args).skip_normalization()
}

#[rustversion::before(2026-05-13)]
pub(crate) fn field_ty<'tcx>(
    field: &middle::ty::FieldDef,
    tcx: middle::ty::TyCtxt<'tcx>,
    args: middle::ty::GenericArgsRef<'tcx>,
) -> middle::ty::Ty<'tcx> {
    field.ty(tcx, args)
}
