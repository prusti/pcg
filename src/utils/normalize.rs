//! Normalization of associated types that keeps the regions of a type.

use crate::{
    rustc_interface::{
        field_ty,
        hir::def_id::DefId,
        infer::{
            infer::{InferCtxt, TyCtxtInferExt, resolve::OpportunisticRegionResolver},
            traits::ObligationCause,
        },
        middle::ty::{self, TypeFoldable, TypeVisitableExt},
        span::DUMMY_SP,
        trait_selection::{
            infer::RegionVariableOrigin,
            traits::{NormalizeExt, ScrubbedTraitError},
        },
    },
    utils::HasCompilerCtxt,
};

#[rustversion::since(2026-08-04)]
use crate::rustc_interface::trait_selection::traits::FulfillmentEngine;
#[rustversion::before(2026-08-04)]
use crate::rustc_interface::trait_selection::traits::{TraitEngine, TraitEngineExt};

/// The type of `field` instantiated with `args`, with its associated types
/// normalized in the typing environment of the function `ctxt` analyses.
///
/// An ADT's field types are written in terms of its generic parameters, so
/// instantiating them can produce an associated type that the body sees as a
/// concrete type, e.g. `<IterMut<'a, i32> as Iterator>::Item` for a field of
/// type `I::Item` with `I = IterMut<'a, i32>`. Normalizing it to
/// `&'a mut i32` makes the regions of the field's type regions of the ADT's
/// type, which the lifetime projections of the field rely on.
pub(crate) fn normalized_field_ty<'a, 'tcx: 'a>(
    field: &ty::FieldDef,
    args: ty::GenericArgsRef<'tcx>,
    ctxt: impl HasCompilerCtxt<'a, 'tcx>,
) -> ty::Ty<'tcx> {
    normalize_keeping_regions(
        field_ty(field, ctxt.tcx(), args),
        ctxt.body().source.def_id(),
        ctxt.tcx(),
    )
}

/// `ty` with its associated types normalized in the typing environment of
/// `def_id`, such that each region of the result is a region of `ty`.
///
/// Normalizing an associated type with an impl instantiates the impl's
/// lifetimes with inference variables and equates the impl's trait reference
/// with the associated type's trait reference. Each lifetime of the impl that
/// the normalized type mentions appears in the impl's trait reference, so
/// equating the two unifies the lifetime's variable with a region of `ty`. To
/// read off which one, the regions of `ty` are replaced by inference
/// variables before normalizing, and each region of the result is mapped back
/// to the region of `ty` its variable is unified with.
///
/// Returns `ty` unchanged if it cannot be normalized, or if a region of the
/// result is neither `'static` nor unified with a region of `ty`. The latter
/// happens when a where clause of the function determines the associated
/// type, e.g. `I: Iterator<Item = &'a mut i32>`: the result then mentions the
/// lifetime parameter `'a` instead of one of the borrow checker's region
/// variables, in which the types of the body's places are written.
#[rustversion::since(2025-05-24)]
fn normalize_keeping_regions<'tcx>(
    ty: ty::Ty<'tcx>,
    def_id: DefId,
    tcx: ty::TyCtxt<'tcx>,
) -> ty::Ty<'tcx> {
    if !ty.has_aliases() {
        return ty;
    }
    let (infcx, param_env) = tcx
        .infer_ctxt()
        .build_with_typing_env(ty::TypingEnv::non_body_analysis(tcx, def_id));
    // The region of `ty` that each variable stands for.
    let mut vars: Vec<(ty::Region<'tcx>, ty::Region<'tcx>)> = Vec::new();
    let with_vars = ty::fold_regions(tcx, ty, |region, _| {
        if let Some((_, var)) = vars.iter().find(|(r, _)| *r == region) {
            *var
        } else {
            let var = infcx.next_region_var(RegionVariableOrigin::Misc(DUMMY_SP));
            vars.push((region, var));
            var
        }
    });
    let Ok(normalized) = deeply_normalize(&infcx, param_env, with_vars) else {
        return ty;
    };
    let mut resolver = OpportunisticRegionResolver::new(&infcx);
    for (_, var) in &mut vars {
        *var = var.fold_with(&mut resolver);
    }
    let mut all_mapped = true;
    let result = ty::fold_regions(tcx, normalized, |region, _| {
        let resolved = region.fold_with(&mut resolver);
        if let Some((original, _)) = vars.iter().find(|(_, var)| *var == resolved) {
            *original
        } else {
            all_mapped &= region.is_static();
            region
        }
    });
    if all_mapped { result } else { ty }
}

/// Toolchains before 2025-05-24 lack `TypingEnv`; there the type is not
/// normalized.
#[rustversion::before(2025-05-24)]
fn normalize_keeping_regions<'tcx>(
    ty: ty::Ty<'tcx>,
    _def_id: DefId,
    _tcx: ty::TyCtxt<'tcx>,
) -> ty::Ty<'tcx> {
    ty
}

/// `value` with its associated types normalized in `infcx`, or the errors of
/// the obligations that normalization could not fulfill.
#[rustversion::since(2026-08-04)]
pub(crate) fn deeply_normalize<'tcx, T: TypeFoldable<ty::TyCtxt<'tcx>>>(
    infcx: &InferCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    value: T,
) -> Result<T, Vec<ScrubbedTraitError<'tcx>>> {
    let cause = ObligationCause::dummy();
    let mut fulfill_cx = FulfillmentEngine::<ScrubbedTraitError>::new(infcx);
    infcx
        .at(&cause, param_env)
        .deeply_normalize(ty::Unnormalized::new(value), &mut fulfill_cx)
        .map_err(|errors| errors.into_iter().collect())
}

/// `value` with its associated types normalized in `infcx`, or the errors of
/// the obligations that normalization could not fulfill.
#[rustversion::before(2026-08-04)]
pub(crate) fn deeply_normalize<'tcx, T: TypeFoldable<ty::TyCtxt<'tcx>>>(
    infcx: &InferCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    value: T,
) -> Result<T, Vec<ScrubbedTraitError<'tcx>>> {
    let cause = ObligationCause::dummy();
    let mut fulfill_cx =
        <dyn TraitEngine<ScrubbedTraitError> as TraitEngineExt<ScrubbedTraitError>>::new(infcx);
    infcx
        .at(&cause, param_env)
        .deeply_normalize(value, &mut *fulfill_cx)
}
