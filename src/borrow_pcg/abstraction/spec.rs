//! The flows of a function call, computed from the callee's signature.
//!
//! A call abstracts the callee. After the call, its caller may assume only
//! what the callee's signature lets every body with that signature do: move
//! a loan it received into a place the caller sees afterwards. The spec of a
//! call lists these flows, from each lifetime projection of an argument
//! before the call (an input) to each lifetime projection of the result, or
//! of an argument that the callee can write into, after the call (an output).
//!
//! The same computation gives the spec of a function for its own body and
//! for its callers: [`call_spec`] with the function's identity arguments and
//! its own environment describes its body; with the arguments and types of a
//! call it describes that call. A flow is a path in a graph whose nodes are
//! the signature's lifetimes, instantiated for the call, and whose edges are
//! what the type system lets the callee rely on:
//!
//! - the outlives relations that the callee's where clauses and the
//!   well-formedness of its signature give (`'a: 'b` lets a `'a` loan flow
//!   into a `'b` place);
//! - the relations that proving the callee's trait bounds gives: the impl
//!   that the trait solver selects for a bound equates the regions of the
//!   bound with those of the impl's header and adds the impl's where
//!   clauses. For `impl<'b> Sink<'b> for Vec<&'b String>`, proving
//!   `Vec<&'v String>: Sink<'t>` equates `'v` and `'t`, so `put` may store
//!   the `&'t String` into the vector;
//! - a bound on a type parameter of the analysed function, which its where
//!   clause proves, lets loans of each lifetime it mentions flow into and out
//!   of the part of the parameter's value that it names
//!   ([`GeneralizedLifetime::BoundPart`]): whichever impl the parameter
//!   stands for moves them through its methods;
//! - for closures, the outlives relations between the closure type's regions
//!   that its body needs (see [`CallSpecQuery::closure_outlives`]);
//! - the regions of an alias type's value are among the regions of its
//!   arguments.
//!
//! A type parameter `T` of the callee is instantiated as a whole: a body that
//! is generic over `T` can only move a value of `T` as it is, so the lifetime
//! at a position inside one occurrence of `T` reaches only the lifetime at
//! the same position inside another occurrence. Each region of the
//! instantiated `T` is therefore a single node, shared by all occurrences.

use std::collections::{BTreeSet, VecDeque};

use crate::{
    HasSettings,
    borrow_pcg::{
        abstraction::{
            ArgIdx, ArgIdxOrResult, FunctionCall, FunctionData, FunctionShape, FunctionShapeInput,
            FunctionShapeOutput, MakeFunctionShapeError, body_regions::BodyRegions,
        },
        edge::{
            abstraction::{FunctionCallOrLoop, function::DefinedFnCall},
            kind::BorrowPcgEdgeKind,
        },
        edge_data::EdgeData,
        graph::{BorrowsGraph, loop_abstraction::MaybeRemoteCurrentPlace},
        region_projection::{LifetimeProjection, PcgRegion, PlaceOrConst},
        visitor::{
            BoundLifetime, GeneralizedLifetime, LifetimeEnv, OpaqueTy, alias_region_pairs,
            extract_generalized_lifetimes, is_bound_region, names_part,
        },
    },
    coupling::PcgCoupledEdgeKind,
    pcg::{PcgNode, PcgNodeWithPlace},
    pcg_validity_assert,
    rustc_interface::{
        fn_def_args,
        hir::def_id::DefId,
        index::Idx,
        infer::{
            infer::{InferCtxt, TyCtxtInferExt, resolve::OpportunisticRegionResolver},
            traits::{Obligation, ObligationCause},
        },
        middle::{
            mir,
            ty::{
                self, GenericArgsRef, TypeFoldable, TypeFolder, TypeSuperFoldable,
                TypeSuperVisitable, TypeVisitable, TypeVisitor, Upcast,
            },
        },
        skip_normalization,
        span::DUMMY_SP,
        trait_selection::{
            infer::RegionVariableOrigin,
            traits::{FulfillmentError, ObligationCtxt},
        },
    },
    utils::{
        HasBorrowCheckerCtxt, HasCompilerCtxt, HasLifetimeEnv, Place,
        data_structures::{HashMap, HashSet},
        normalize::deeply_normalize,
        place::{maybe_old::MaybeLabelledPlace, maybe_remote::MaybeRemotePlace},
    },
};

/// The function a call calls.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Callee<'tcx> {
    /// A function item, a method, or a closure body, with the generic
    /// arguments of the call.
    FnDef(DefId, GenericArgsRef<'tcx>),
    /// A function pointer of this type.
    FnPtr(ty::PolyFnSig<'tcx>),
}

/// The data that determines the spec of a call.
pub(crate) struct CallSpecQuery<'a, 'tcx> {
    pub(crate) callee: Callee<'tcx>,
    /// The types of the call's arguments, in `env`.
    pub(crate) arg_tys: &'a [ty::Ty<'tcx>],
    /// The type of the call's result, in `env`.
    pub(crate) result_ty: ty::Ty<'tcx>,
    /// The function the call is in. Its where clauses prove the callee's
    /// bounds that mention its own parameters.
    pub(crate) env: LifetimeEnv<'tcx>,
    /// Whether the body of a closure whose type contains both regions needs
    /// the first to outlive the second. `sup` and `sub` are regions of a
    /// closure type in `env`, or for a closure's own spec, regions of the
    /// closure type, argument types and result type in its body.
    ///
    /// A closure's signature is inferred: rustc's borrow checker computes
    /// which relations between the regions of its captures and its
    /// signature the closure body needs, and requires them where the
    /// closure is created. These relations are the only source of the flows
    /// a closure performs (`|x| v.push(x)` stores `x` into the captured
    /// `v`), so this is the one place where the spec takes a fact from the
    /// borrow checker rather than the type system: a call passes the borrow
    /// checker's outlives relation between the regions of the closure type.
    pub(crate) closure_outlives: &'a dyn Fn(ty::Region<'tcx>, ty::Region<'tcx>) -> bool,
}

/// A node of the flow graph of a call.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Node<'tcx> {
    /// A lifetime projection of an argument before the call.
    Input(ArgIdx, usize),
    /// A lifetime projection of the result, or of an argument after the call.
    Output(ArgIdxOrResult, usize),
    /// A region of the callee's instantiated signature or of the bounds the
    /// trait solver used, after resolving inference variables.
    Region(ty::Region<'tcx>),
    /// A lifetime of an opaque type (a type parameter or alias of `env`) in
    /// the callee's instantiated signature: `RegionsIn` of it, or one of its
    /// parts.
    Opaque(ty::Ty<'tcx>, OpaquePart<'tcx>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum OpaquePart<'tcx> {
    /// All of the value: `RegionsIn` of the opaque type, for moving the value
    /// as a whole.
    Whole,
    /// The part named by a lifetime (see [`GeneralizedLifetime::BoundPart`]).
    Bound(BoundLifetime<'tcx>),
}

/// A lifetime at one position of the callee's instantiated signature.
#[derive(Clone, Copy, Debug)]
enum FormalLifetime<'tcx> {
    Region(ty::Region<'tcx>),
    Part(ty::Ty<'tcx>, OpaquePart<'tcx>),
}

/// The lifetimes at the occurrence `actual` of a type of the call, paired
/// with those at the occurrence `formal` at the same position of the callee's
/// instantiated signature.
///
/// Where one of the two is an opaque type and the other is not, e.g. the
/// opaque return type of a function and the type of the value that its body
/// returns, the value's regions are in the parts of the opaque type's value,
/// so each pairs with each part.
fn paired_lifetimes<'tcx>(
    actual: OccurrenceKind<'tcx>,
    formal: OccurrenceKind<'tcx>,
    env: LifetimeEnv<'tcx>,
) -> Vec<(GeneralizedLifetime<'tcx>, FormalLifetime<'tcx>)> {
    let parts = |ty: ty::Ty<'tcx>, env: LifetimeEnv<'tcx>| {
        env.bound_lifetimes(OpaqueTy::try_from(ty).unwrap())
    };
    match (actual, formal) {
        (OccurrenceKind::Region(actual), OccurrenceKind::Region(formal)) => vec![(
            GeneralizedLifetime::Region(actual.into()),
            FormalLifetime::Region(formal),
        )],
        (OccurrenceKind::Member(opaque, lifetime), formal) => {
            let part =
                GeneralizedLifetime::BoundPart(OpaqueTy::try_from(opaque).unwrap(), lifetime);
            let formal = match formal {
                OccurrenceKind::Region(region) => FormalLifetime::Region(region),
                OccurrenceKind::Opaque(ty) => FormalLifetime::Part(ty, OpaquePart::Whole),
                OccurrenceKind::Member(..) => unreachable!("The signature has no hidden types"),
            };
            vec![(part, formal)]
        }
        (_, OccurrenceKind::Member(..)) => unreachable!("The signature has no hidden types"),
        (OccurrenceKind::Region(actual), OccurrenceKind::Opaque(formal)) => {
            parts(formal, env.for_signature())
                .into_iter()
                .map(|part| {
                    (
                        GeneralizedLifetime::Region(actual.into()),
                        FormalLifetime::Part(formal, OpaquePart::Bound(part)),
                    )
                })
                .collect()
        }
        (OccurrenceKind::Opaque(actual), OccurrenceKind::Region(formal)) => {
            let opaque = OpaqueTy::try_from(actual).unwrap();
            parts(actual, env)
                .into_iter()
                .map(|part| {
                    (
                        GeneralizedLifetime::BoundPart(opaque, part),
                        FormalLifetime::Region(formal),
                    )
                })
                .collect()
        }
        (OccurrenceKind::Opaque(actual), OccurrenceKind::Opaque(formal)) => {
            let opaque = OpaqueTy::try_from(actual).unwrap();
            let mut pairs = vec![(
                GeneralizedLifetime::RegionsIn(opaque),
                FormalLifetime::Part(formal, OpaquePart::Whole),
            )];
            pairs.extend(paired_parts(actual, formal, env).into_iter().map(
                |(actual_part, formal_part)| {
                    (
                        GeneralizedLifetime::BoundPart(opaque, actual_part),
                        FormalLifetime::Part(formal, OpaquePart::Bound(formal_part)),
                    )
                },
            ));
            pairs
        }
    }
}

/// The lifetimes naming the parts of the opaque types `actual` and `formal`
/// at the same position (see [`LifetimeEnv::bound_lifetimes`]), paired. The
/// lifetimes of where clauses are the same in both, `formal`'s named as in a
/// signature; those of the arguments of an alias type correspond by position
/// in the arguments.
fn paired_parts<'tcx>(
    actual: ty::Ty<'tcx>,
    formal: ty::Ty<'tcx>,
    env: LifetimeEnv<'tcx>,
) -> Vec<(BoundLifetime<'tcx>, BoundLifetime<'tcx>)> {
    let (actual_opaque, formal_opaque) = (
        OpaqueTy::try_from(actual).unwrap(),
        OpaqueTy::try_from(formal).unwrap(),
    );
    let formal_clause_lifetimes = env.for_signature().where_clause_lifetimes(formal_opaque);
    let mut pairs: Vec<(BoundLifetime<'tcx>, BoundLifetime<'tcx>)> = env
        .where_clause_lifetimes(actual_opaque)
        .into_iter()
        .filter_map(|lifetime| {
            let formal = env.to_signature(lifetime);
            formal_clause_lifetimes
                .contains(&formal)
                .then_some((lifetime, formal))
        })
        .collect();
    let (ty::TyKind::Alias(_, actual_alias), ty::TyKind::Alias(_, formal_alias)) =
        (actual.kind(), formal.kind())
    else {
        return pairs;
    };
    for (actual_arg, formal_arg) in actual_alias.args.iter().zip(formal_alias.args.iter()) {
        if let (Some(actual_region), Some(formal_region)) =
            (actual_arg.as_region(), formal_arg.as_region())
        {
            if names_part(actual_region) && names_part(formal_region) {
                pairs.push((
                    BoundLifetime::Region(actual_region.into()),
                    BoundLifetime::Region(formal_region.into()),
                ));
            }
        } else if let (Some(actual_ty), Some(formal_ty)) =
            (actual_arg.as_type(), formal_arg.as_type())
        {
            for (actual, formal) in aligned_occurrences(actual_ty, formal_ty, env.tcx) {
                pairs.extend(member_pairs(actual, formal, env));
            }
        }
    }
    pairs
}

/// The lifetimes that the occurrences `actual` and `formal` at the same
/// position of the arguments of two alias types give their parts, paired.
fn member_pairs<'tcx>(
    actual: OccurrenceKind<'tcx>,
    formal: OccurrenceKind<'tcx>,
    env: LifetimeEnv<'tcx>,
) -> Vec<(BoundLifetime<'tcx>, BoundLifetime<'tcx>)> {
    let lifetime = |occurrence: OccurrenceKind<'tcx>| match occurrence {
        OccurrenceKind::Region(region) if !names_part(region) => None,
        OccurrenceKind::Region(region) => Some(BoundLifetime::Region(region.into())),
        OccurrenceKind::Opaque(ty) => {
            Some(BoundLifetime::RegionsIn(OpaqueTy::try_from(ty).unwrap()))
        }
        // An argument of an alias type that is itself in a hidden type
        // names no part of the alias's value.
        OccurrenceKind::Member(..) => None,
    };
    let mut pairs: Vec<_> = lifetime(actual).zip(lifetime(formal)).into_iter().collect();
    if let (OccurrenceKind::Opaque(actual), OccurrenceKind::Opaque(formal)) = (actual, formal) {
        pairs.extend(paired_parts(actual, formal, env));
    }
    pairs
}

impl<'tcx> OpaquePart<'tcx> {
    /// This part with its region resolved by `resolver`.
    fn resolve(
        self,
        resolver: &mut OpportunisticRegionResolver<'_, 'tcx>,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Self {
        match self {
            OpaquePart::Bound(BoundLifetime::Region(region)) => OpaquePart::Bound(
                BoundLifetime::Region(region.rust_region(tcx).fold_with(resolver).into()),
            ),
            OpaquePart::Bound(BoundLifetime::RegionsIn(opaque)) => {
                OpaquePart::Bound(BoundLifetime::RegionsIn(
                    OpaqueTy::try_from(opaque.ty(tcx).fold_with(resolver)).unwrap(),
                ))
            }
            OpaquePart::Whole => OpaquePart::Whole,
        }
    }
}

/// A region or an opaque type at one position of a type, and whether the
/// callee can write into it when the type is the type of an argument.
#[derive(Clone, Copy, Debug)]
struct Occurrence<'tcx> {
    kind: OccurrenceKind<'tcx>,
    writable: bool,
}

#[derive(Clone, Copy, Debug)]
enum OccurrenceKind<'tcx> {
    Region(ty::Region<'tcx>),
    /// A type parameter or an alias type.
    Opaque(ty::Ty<'tcx>),
    /// A region or opaque type of the hidden type of an opaque type (the
    /// first field), which names a part of its value (see
    /// [`aligned_occurrences`]).
    Member(ty::Ty<'tcx>, BoundLifetime<'tcx>),
}

/// The regions and opaque types of `ty`, one entry per position, in an order
/// that depends only on the shape of `ty`: two types that are equal up to
/// regions have their entries at the same indices. Regions bound inside
/// `ty` are skipped. An opaque type is a single entry; its contents are
/// unknown.
///
/// A position is writable if it is invariant in `ty`: behind a `&mut`, in an
/// invariant argument of an ADT such as `Cell<T>`, in the trait of a `dyn`
/// type, or in an opaque type, whose value may contain any of these.
fn occurrences<'tcx>(ty: ty::Ty<'tcx>, tcx: ty::TyCtxt<'tcx>) -> Vec<Occurrence<'tcx>> {
    let mut walker = OccurrenceWalker {
        tcx,
        variance: ty::Variance::Covariant,
        occurrences: Vec::new(),
    };
    walker.walk(ty);
    walker.occurrences
}

/// The lifetimes of `ty` in `env` that the callee can write into when `ty`
/// is the type of an argument: those at a writable position (see
/// [`occurrences`]).
fn writable_lifetimes<'tcx>(
    ty: ty::Ty<'tcx>,
    env: LifetimeEnv<'tcx>,
) -> HashSet<GeneralizedLifetime<'tcx>> {
    let mut writable = HashSet::default();
    for occurrence in occurrences(ty, env.tcx) {
        if !occurrence.writable {
            continue;
        }
        match occurrence.kind {
            OccurrenceKind::Region(region) => {
                writable.insert(GeneralizedLifetime::Region(region.into()));
            }
            OccurrenceKind::Opaque(opaque) => {
                let opaque = OpaqueTy::try_from(opaque).unwrap();
                writable.insert(GeneralizedLifetime::RegionsIn(opaque));
                for lifetime in env.bound_lifetimes(opaque) {
                    writable.insert(GeneralizedLifetime::BoundPart(opaque, lifetime));
                }
            }
            OccurrenceKind::Member(..) => unreachable!("`occurrences` reveals no hidden types"),
        }
    }
    writable
}

/// The regions and opaque types of `actual` paired with those at the same
/// positions of `formal`, a type that is equal to `actual` up to regions and
/// opaque types. Where one of the two has an opaque type and the other does
/// not, e.g. the opaque return type of a function and the type of the value
/// that its body returns, the opaque type is paired with each region and
/// opaque type of the other's type at that position.
fn aligned_occurrences<'tcx>(
    actual: ty::Ty<'tcx>,
    formal: ty::Ty<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
) -> Vec<(OccurrenceKind<'tcx>, OccurrenceKind<'tcx>)> {
    let mut pairs = Vec::new();
    align(actual, formal, tcx, &mut pairs);
    pairs
}

fn align<'tcx>(
    actual: ty::Ty<'tcx>,
    formal: ty::Ty<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    pairs: &mut Vec<(OccurrenceKind<'tcx>, OccurrenceKind<'tcx>)>,
) {
    use crate::rustc_interface::middle::ty::GenericArgKind;
    let mismatch =
        || -> ! { panic!("The type {actual:?} of a call does not have the shape of {formal:?}") };
    let is_opaque = |ty: ty::Ty<'tcx>| OpaqueTy::try_from(ty).is_ok();
    match (is_opaque(actual), is_opaque(formal)) {
        (true, true) => {
            pairs.push((
                OccurrenceKind::Opaque(actual),
                OccurrenceKind::Opaque(formal),
            ));
            return;
        }
        // In the scope that defines an opaque type, a value of its hidden type
        // can be written into a place of the opaque type. The hidden type is
        // written in the opaque type's arguments, so its regions name parts
        // of the opaque type's value.
        (true, false) if let Some((def_id, args)) = opaque_type(actual) => {
            let hidden = instantiate(tcx.type_of(def_id).skip_binder(), tcx, args);
            let mut hidden_pairs = Vec::new();
            align(hidden, formal, tcx, &mut hidden_pairs);
            pairs.extend(hidden_pairs.into_iter().filter_map(|(member, formal)| {
                let lifetime = match member {
                    OccurrenceKind::Region(region) => BoundLifetime::Region(region.into()),
                    OccurrenceKind::Opaque(ty) => {
                        BoundLifetime::RegionsIn(OpaqueTy::try_from(ty).unwrap())
                    }
                    OccurrenceKind::Member(..) => return None,
                };
                Some((OccurrenceKind::Member(actual, lifetime), formal))
            }));
            return;
        }
        (true, false) => {
            let paired = occurrences(formal, tcx)
                .into_iter()
                .map(|occurrence| (OccurrenceKind::Opaque(actual), occurrence.kind));
            pairs.extend(paired);
            return;
        }
        (false, true) => {
            let paired = occurrences(actual, tcx)
                .into_iter()
                .map(|occurrence| (occurrence.kind, OccurrenceKind::Opaque(formal)));
            pairs.extend(paired);
            return;
        }
        (false, false) => {}
    }
    if std::mem::discriminant(actual.kind()) != std::mem::discriminant(formal.kind()) {
        mismatch();
    }
    let (actual_children, formal_children) = (children(actual), children(formal));
    if actual_children.len() != formal_children.len() {
        mismatch();
    }
    for (actual_child, formal_child) in actual_children.into_iter().zip(formal_children) {
        match (actual_child.kind(), formal_child.kind()) {
            (GenericArgKind::Type(actual_ty), GenericArgKind::Type(formal_ty)) => {
                align(actual_ty, formal_ty, tcx, pairs);
            }
            // A region bound inside one of the types names no data, and no
            // lifetime of the type covers it: a `for<'x> fn(&'x u8)` argument
            // passed for a `fn(&'a u8)` parameter pairs with nothing.
            (GenericArgKind::Lifetime(actual_region), GenericArgKind::Lifetime(formal_region)) => {
                if !is_bound_region(actual_region) && !is_bound_region(formal_region) {
                    pairs.push((
                        OccurrenceKind::Region(actual_region),
                        OccurrenceKind::Region(formal_region),
                    ));
                }
            }
            (GenericArgKind::Const(_), GenericArgKind::Const(_)) => {}
            _ => mismatch(),
        }
    }
}

/// The definition and arguments of `ty`, if it is an opaque type.
#[rustversion::since(2026-08-01)]
fn opaque_type(ty: ty::Ty<'_>) -> Option<(DefId, GenericArgsRef<'_>)> {
    match ty.kind() {
        ty::TyKind::Alias(_, alias) => match alias.kind {
            ty::AliasTyKind::Opaque { def_id } => Some((def_id, alias.args)),
            _ => None,
        },
        _ => None,
    }
}

/// The definition and arguments of `ty`, if it is an opaque type.
#[rustversion::before(2026-08-01)]
fn opaque_type(ty: ty::Ty<'_>) -> Option<(DefId, GenericArgsRef<'_>)> {
    match ty.kind() {
        ty::TyKind::Alias(ty::AliasTyKind::Opaque, alias) => Some((alias.def_id, alias.args)),
        _ => None,
    }
}

/// The types, regions and constants that `ty` is directly made of, in the
/// order in which a type visitor visits them, with repetitions.
fn children(ty: ty::Ty<'_>) -> Vec<ty::GenericArg<'_>> {
    struct Children<'tcx>(Vec<ty::GenericArg<'tcx>>);
    impl<'tcx> TypeVisitor<ty::TyCtxt<'tcx>> for Children<'tcx> {
        fn visit_ty(&mut self, ty: ty::Ty<'tcx>) {
            self.0.push(ty.into());
        }
        fn visit_region(&mut self, region: ty::Region<'tcx>) {
            self.0.push(region.into());
        }
        fn visit_const(&mut self, constant: ty::Const<'tcx>) {
            self.0.push(constant.into());
        }
    }
    let mut children = Children(Vec::new());
    ty.super_visit_with(&mut children);
    children.0
}

struct OccurrenceWalker<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    /// The variance of the current position in the outermost type.
    variance: ty::Variance,
    occurrences: Vec<Occurrence<'tcx>>,
}

impl<'tcx> OccurrenceWalker<'tcx> {
    fn with_variance(&mut self, variance: ty::Variance, f: impl FnOnce(&mut Self)) {
        let outer = self.variance;
        self.variance = outer.xform(variance);
        f(self);
        self.variance = outer;
    }

    fn walk(&mut self, ty: ty::Ty<'tcx>) {
        match ty.kind() {
            ty::TyKind::Param(_) | ty::TyKind::Alias(..) => self.occurrences.push(Occurrence {
                kind: OccurrenceKind::Opaque(ty),
                writable: true,
            }),
            ty::TyKind::Ref(region, referent, mutability) => {
                self.visit_region(*region);
                let variance = if mutability.is_mut() {
                    ty::Variance::Invariant
                } else {
                    ty::Variance::Covariant
                };
                self.with_variance(variance, |walker| walker.walk(*referent));
            }
            ty::TyKind::RawPtr(pointee, mutability) => {
                let variance = if mutability.is_mut() {
                    ty::Variance::Invariant
                } else {
                    ty::Variance::Covariant
                };
                self.with_variance(variance, |walker| walker.walk(*pointee));
            }
            ty::TyKind::Adt(adt_def, args) => {
                let variances = self.tcx.variances_of(adt_def.did());
                for (arg, variance) in args.iter().zip(variances.iter()) {
                    self.with_variance(*variance, |walker| arg.visit_with(walker));
                }
            }
            ty::TyKind::Tuple(_)
            | ty::TyKind::Array(..)
            | ty::TyKind::Slice(_)
            | ty::TyKind::Pat(..) => ty.super_visit_with(self),
            ty::TyKind::Dynamic(predicates, region, ..) => {
                self.visit_region(*region);
                self.with_variance(ty::Variance::Invariant, |walker| {
                    predicates.visit_with(walker);
                });
            }
            // Function and closure types, and the rest: their regions are
            // treated as invariant.
            _ => self.with_variance(ty::Variance::Invariant, |walker| {
                ty.super_visit_with(walker);
            }),
        }
    }
}

impl<'tcx> TypeVisitor<ty::TyCtxt<'tcx>> for OccurrenceWalker<'tcx> {
    fn visit_ty(&mut self, ty: ty::Ty<'tcx>) {
        self.walk(ty);
    }

    fn visit_region(&mut self, region: ty::Region<'tcx>) {
        if !is_bound_region(region) {
            self.occurrences.push(Occurrence {
                kind: OccurrenceKind::Region(region),
                writable: self.variance == ty::Variance::Invariant,
            });
        }
    }
}

/// Replaces the free regions of the values it folds by inference variables,
/// the same region by the same variable, and remembers for each variable the
/// region it replaced. For each closure type it folds, it remembers which
/// variables replaced the regions of that closure type.
struct RegionsToVars<'a, 'tcx> {
    infcx: &'a InferCtxt<'tcx>,
    vars: HashMap<ty::Region<'tcx>, ty::Region<'tcx>>,
    /// The variables this folder created.
    introduced: HashSet<ty::Region<'tcx>>,
    /// The original regions of each folded closure type, with their
    /// variables.
    closures: Vec<Vec<(ty::Region<'tcx>, ty::Region<'tcx>)>>,
}

impl<'tcx> TypeFolder<ty::TyCtxt<'tcx>> for RegionsToVars<'_, 'tcx> {
    fn cx(&self) -> ty::TyCtxt<'tcx> {
        self.infcx.tcx
    }

    fn fold_ty(&mut self, ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        let folded = ty.super_fold_with(self);
        if let ty::TyKind::Closure(..) = ty.kind() {
            let mut regions = Vec::new();
            self.infcx.tcx.for_each_free_region(&ty, |region| {
                if let Some(var) = self.vars.get(&region)
                    && !regions.iter().any(|(r, _)| *r == region)
                {
                    regions.push((region, *var));
                }
            });
            self.closures.push(regions);
        }
        folded
    }

    fn fold_region(&mut self, region: ty::Region<'tcx>) -> ty::Region<'tcx> {
        match region.kind() {
            // Erased regions are left for the closure signature, which gives
            // them regions of their own (see `FunctionData::closure_fn_sig`).
            ty::RegionKind::ReBound(..) | ty::RegionKind::ReStatic | ty::RegionKind::ReErased => {
                region
            }
            _ if self.introduced.contains(&region) => region,
            _ => self.var_for(region),
        }
    }
}

impl<'tcx> RegionsToVars<'_, 'tcx> {
    fn var_for(&mut self, region: ty::Region<'tcx>) -> ty::Region<'tcx> {
        if let Some(var) = self.vars.get(&region) {
            return *var;
        }
        let var = self.fresh_var();
        self.vars.insert(region, var);
        var
    }

    fn fresh_var(&mut self) -> ty::Region<'tcx> {
        let var = self
            .infcx
            .next_region_var(RegionVariableOrigin::Misc(DUMMY_SP));
        self.introduced.insert(var);
        var
    }
}

/// The flow graph of a call, built up from the facts of the callee's
/// signature and the trait solver.
struct FlowGraph<'tcx> {
    successors: HashMap<Node<'tcx>, BTreeSet<usize>>,
    nodes: Vec<Node<'tcx>>,
    indices: HashMap<Node<'tcx>, usize>,
}

impl<'tcx> FlowGraph<'tcx> {
    fn new() -> Self {
        Self {
            successors: HashMap::default(),
            nodes: Vec::new(),
            indices: HashMap::default(),
        }
    }

    fn index(&mut self, node: Node<'tcx>) -> usize {
        if let Some(index) = self.indices.get(&node) {
            return *index;
        }
        let index = self.nodes.len();
        self.nodes.push(node);
        self.indices.insert(node, index);
        index
    }

    /// Loans in `from` may flow into `to`.
    fn add_flow(&mut self, from: Node<'tcx>, to: Node<'tcx>) {
        if from == to {
            return;
        }
        let to = self.index(to);
        self.index(from);
        self.successors.entry(from).or_default().insert(to);
    }

    fn add_flows_both_ways(&mut self, a: Node<'tcx>, b: Node<'tcx>) {
        self.add_flow(a, b);
        self.add_flow(b, a);
    }

    /// The region nodes that `from` reaches through region nodes only: the
    /// outlives relation between regions that the graph gives.
    fn reachable_regions(&self, from: Node<'tcx>) -> HashSet<Node<'tcx>> {
        let mut seen: HashSet<Node<'tcx>> = HashSet::from_iter([from]);
        let mut stack = vec![from];
        while let Some(node) = stack.pop() {
            for &successor in self.successors.get(&node).into_iter().flatten() {
                let successor = self.nodes[successor];
                if matches!(successor, Node::Region(_)) && seen.insert(successor) {
                    stack.push(successor);
                }
            }
        }
        seen
    }

    /// The outputs that loans in `from` may flow into through region nodes
    /// only, i.e. by the outlives relations between regions alone.
    fn outputs_through_regions(&self, from: Node<'tcx>) -> Vec<(ArgIdxOrResult, usize)> {
        let mut seen: HashSet<Node<'tcx>> = HashSet::from_iter([from]);
        let mut stack = vec![from];
        let mut outputs = Vec::new();
        while let Some(node) = stack.pop() {
            for &successor in self.successors.get(&node).into_iter().flatten() {
                let successor = self.nodes[successor];
                match successor {
                    Node::Output(base, idx) => outputs.push((base, idx)),
                    Node::Region(_) if seen.insert(successor) => stack.push(successor),
                    _ => {}
                }
            }
        }
        outputs
    }

    /// The outputs that loans in `from` may flow into.
    fn reachable_outputs(&self, from: Node<'tcx>) -> Vec<(ArgIdxOrResult, usize)> {
        let mut seen: BTreeSet<usize> = BTreeSet::new();
        let mut queue: VecDeque<Node<'tcx>> = VecDeque::from([from]);
        let mut outputs = Vec::new();
        while let Some(node) = queue.pop_front() {
            if let Node::Output(base, idx) = node {
                outputs.push((base, idx));
            }
            for &successor in self.successors.get(&node).into_iter().flatten() {
                if seen.insert(successor) {
                    queue.push_back(self.nodes[successor]);
                }
            }
        }
        outputs
    }
}

/// The relations that proving some obligations gave: pairs `(sup, sub)` of
/// regions where `sup` must outlive `sub`, and pairs `(ty, region)` where
/// `ty` must outlive `region`.
struct SolvedRelations<'tcx> {
    region_outlives: Vec<(ty::Region<'tcx>, ty::Region<'tcx>)>,
    type_outlives: Vec<(ty::Ty<'tcx>, ty::Region<'tcx>)>,
}

/// Proves `predicates` in `infcx` and returns the region relations that
/// proving them requires. Panics if they cannot be proven: rustc accepted
/// the program, so it proved them at the call.
fn solve<'tcx>(
    infcx: &InferCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    predicates: impl IntoIterator<Item = ty::Predicate<'tcx>>,
) -> SolvedRelations<'tcx> {
    let ocx = ObligationCtxt::new_with_diagnostics(infcx);
    for predicate in predicates {
        ocx.register_obligation(Obligation::new(
            infcx.tcx,
            ObligationCause::dummy(),
            param_env,
            predicate,
        ));
    }
    let errors = prove_all(&ocx);
    assert!(
        errors.is_empty(),
        "The trait solver could not prove the bounds of a call that rustc accepted: {errors:?}"
    );
    let type_outlives = infcx
        .take_registered_region_obligations()
        .into_iter()
        .map(|obligation| (obligation.sup_type, obligation.sub_region))
        .collect();
    // Solving may also register region assumptions, which are no relations
    // of the call; rustc takes the region constraints (`region_outlives`) only
    // once they are taken.
    infcx.take_registered_region_assumptions();
    SolvedRelations {
        region_outlives: region_outlives(infcx),
        type_outlives,
    }
}

#[rustversion::since(2026-04-19)]
fn is_c_variadic(sig: ty::FnSig<'_>) -> bool {
    sig.c_variadic()
}

#[rustversion::before(2026-04-19)]
fn is_c_variadic(sig: ty::FnSig<'_>) -> bool {
    sig.c_variadic
}

/// The errors of the obligations registered in `ocx` that cannot be proven.
#[rustversion::since(2026-08-01)]
fn prove_all<'tcx>(
    ocx: &ObligationCtxt<'_, 'tcx, FulfillmentError<'tcx>>,
) -> Vec<FulfillmentError<'tcx>> {
    use crate::rustc_interface::infer::traits::TraitErrors;
    match ocx.evaluate_obligations_error_on_ambiguity() {
        TraitErrors::HasErrors(errors) => errors.into_iter().collect(),
        TraitErrors::NoErrors => Vec::new(),
    }
}

/// The errors of the obligations registered in `ocx` that cannot be proven.
#[rustversion::before(2026-08-01)]
fn prove_all<'tcx>(
    ocx: &ObligationCtxt<'_, 'tcx, FulfillmentError<'tcx>>,
) -> Vec<FulfillmentError<'tcx>> {
    ocx.select_all_or_error()
}

/// `value`, whose generic parameters are those of the item it belongs to,
/// with these parameters instantiated with `args`.
#[rustversion::since(2026-08-01)]
fn instantiate<'tcx, T: TypeFoldable<ty::TyCtxt<'tcx>>>(
    value: T,
    tcx: ty::TyCtxt<'tcx>,
    args: GenericArgsRef<'tcx>,
) -> T {
    skip_normalization(ty::EarlyBinder::bind(tcx, value).instantiate(tcx, args))
}

/// `value`, whose generic parameters are those of the item it belongs to,
/// with these parameters instantiated with `args`.
#[rustversion::before(2026-08-01)]
fn instantiate<'tcx, T: TypeFoldable<ty::TyCtxt<'tcx>>>(
    value: T,
    tcx: ty::TyCtxt<'tcx>,
    args: GenericArgsRef<'tcx>,
) -> T {
    skip_normalization(ty::EarlyBinder::bind(value).instantiate(tcx, args))
}

/// The `(sup, sub)` pairs of the region constraints recorded in `infcx`
/// since the last call, an equality giving both pairs.
#[rustversion::since(2026-07-01)]
fn region_outlives<'tcx>(infcx: &InferCtxt<'tcx>) -> Vec<(ty::Region<'tcx>, ty::Region<'tcx>)> {
    use crate::rustc_interface::infer::infer::region_constraints::ConstraintKind;
    infcx
        .take_and_reset_region_constraints()
        .constraints
        .into_iter()
        .flat_map(|(constraint, _)| match constraint.kind {
            ConstraintKind::VarEqVar | ConstraintKind::VarEqReg | ConstraintKind::RegEqReg => {
                vec![
                    (constraint.sup, constraint.sub),
                    (constraint.sub, constraint.sup),
                ]
            }
            ConstraintKind::VarSubVar
            | ConstraintKind::RegSubVar
            | ConstraintKind::VarSubReg
            | ConstraintKind::RegSubReg => vec![(constraint.sup, constraint.sub)],
        })
        .collect()
}

#[rustversion::all(since(2025-09-01), before(2026-07-01))]
fn region_outlives<'tcx>(infcx: &InferCtxt<'tcx>) -> Vec<(ty::Region<'tcx>, ty::Region<'tcx>)> {
    infcx
        .take_and_reset_region_constraints()
        .constraints
        .into_iter()
        .map(|(constraint, _)| (constraint.sup, constraint.sub))
        .collect()
}

#[rustversion::before(2025-09-01)]
fn region_outlives<'tcx>(infcx: &InferCtxt<'tcx>) -> Vec<(ty::Region<'tcx>, ty::Region<'tcx>)> {
    use crate::rustc_interface::infer::infer::region_constraints::Constraint;
    let tcx = infcx.tcx;
    let var = |vid| ty::Region::new_var(tcx, vid);
    infcx
        .take_and_reset_region_constraints()
        .constraints
        .into_iter()
        .map(|(constraint, _)| match constraint {
            Constraint::VarSubVar(sub, sup) => (var(sup), var(sub)),
            Constraint::RegSubVar(sub, sup) => (var(sup), sub),
            Constraint::VarSubReg(sub, sup) => (sup, var(sub)),
            Constraint::RegSubReg(sub, sup) => (sup, sub),
        })
        .collect()
}

/// The instantiated signature of `callee`, its regions replaced by inference
/// variables of `folder`, and the where clauses it may rely on.
fn instantiate_callee<'tcx>(
    callee: Callee<'tcx>,
    folder: &mut RegionsToVars<'_, 'tcx>,
) -> (ty::FnSig<'tcx>, Vec<ty::Clause<'tcx>>, Vec<ty::Ty<'tcx>>) {
    let tcx = folder.infcx.tcx;
    match callee {
        Callee::FnDef(def_id, args) => {
            let args = args.fold_with(folder);
            let sig = FunctionData::new(def_id)
                .fn_sig(tcx, args)
                .fold_with(folder);
            let clauses = tcx
                .param_env(def_id)
                .caller_bounds()
                .iter()
                .map(|clause| instantiate(clause, tcx, args))
                .collect();
            let wf_types = sig
                .inputs_and_output
                .iter()
                .chain(
                    header_types(def_id, tcx)
                        .into_iter()
                        .map(|ty| instantiate(ty, tcx, args)),
                )
                .collect();
            (sig, clauses, wf_types)
        }
        Callee::FnPtr(poly_sig) => {
            let sig = tcx
                .instantiate_bound_regions(poly_sig, |_| folder.fresh_var())
                .0
                .fold_with(folder);
            (sig, Vec::new(), Vec::new())
        }
    }
}

/// For a method of an impl or a trait, the types of the header of the impl or
/// trait that the method may assume to be well-formed, in the generic
/// parameters of the impl or trait: the self type of an inherent impl, the
/// arguments of the trait of a trait impl (as rustc's `assumed_wf_types`),
/// and for a trait method those of the trait, which the impl that a call
/// selects assumes and the caller proves. `Ctx::<'a, 'b>::f` may assume
/// `'b: 'a` for `struct Ctx<'a, 'b>(&'a &'b u32)`, and so may
/// `<&'a &'b () as Tr<'a, 'b>>::f`.
fn header_types(def_id: DefId, tcx: ty::TyCtxt<'_>) -> Vec<ty::Ty<'_>> {
    use crate::rustc_interface::hir::def::DefKind;
    let Some(parent) = tcx.opt_parent(def_id) else {
        return Vec::new();
    };
    match tcx.def_kind(parent) {
        DefKind::Impl { of_trait: true } => {
            let trait_ref = TraitRefOfImpl::trait_ref(tcx.impl_trait_ref(parent));
            trait_ref.skip_binder().args.types().collect()
        }
        DefKind::Impl { of_trait: false } => {
            vec![skip_normalization(
                tcx.type_of(parent).instantiate_identity(),
            )]
        }
        DefKind::Trait => ty::GenericArgs::identity_for_item(tcx, parent)
            .types()
            .collect(),
        _ => Vec::new(),
    }
}

/// The trait ref of a trait impl, which `TyCtxt::impl_trait_ref` returns
/// wrapped in an `Option` on older toolchains.
trait TraitRefOfImpl<'tcx> {
    fn trait_ref(self) -> ty::EarlyBinder<'tcx, ty::TraitRef<'tcx>>;
}

impl<'tcx> TraitRefOfImpl<'tcx> for ty::EarlyBinder<'tcx, ty::TraitRef<'tcx>> {
    fn trait_ref(self) -> ty::EarlyBinder<'tcx, ty::TraitRef<'tcx>> {
        self
    }
}

impl<'tcx> TraitRefOfImpl<'tcx> for Option<ty::EarlyBinder<'tcx, ty::TraitRef<'tcx>>> {
    fn trait_ref(self) -> ty::EarlyBinder<'tcx, ty::TraitRef<'tcx>> {
        self.expect("a trait impl has a trait ref")
    }
}

/// The flow graph of a call (see the module documentation).
struct SpecGraph<'tcx> {
    graph: FlowGraph<'tcx>,
    /// All lifetime projections of the call's arguments.
    inputs: Vec<(ArgIdx, usize)>,
    /// The lifetime projections of the result, and those of the arguments
    /// that the callee can write into.
    outputs: BTreeSet<(ArgIdxOrResult, usize)>,
    /// The node of each region of the callee's instantiated signature and
    /// bounds, by the region it has in them.
    region_nodes: HashMap<ty::Region<'tcx>, Node<'tcx>>,
    /// The nodes that the lifetime projections of the arguments and result
    /// are bound to, with their lifetimes.
    bindings: Vec<(
        (ArgIdxOrResult, usize),
        GeneralizedLifetime<'tcx>,
        Node<'tcx>,
    )>,
}

#[rustversion::since(2025-05-24)]
fn spec_graph<'tcx>(query: &CallSpecQuery<'_, 'tcx>) -> SpecGraph<'tcx> {
    let env = query.env;
    let tcx = env.tcx;
    let (infcx, param_env) = tcx
        .infer_ctxt()
        .build_with_typing_env(ty::TypingEnv::non_body_analysis(tcx, env.def_id));
    let mut folder = RegionsToVars {
        infcx: &infcx,
        vars: HashMap::default(),
        introduced: HashSet::default(),
        closures: Vec::new(),
    };
    let (sig, clauses, wf_types) = instantiate_callee(query.callee, &mut folder);
    let formal_tys =
        deeply_normalize(&infcx, param_env, sig.inputs_and_output).unwrap_or_else(|errors| {
            panic!("Cannot normalize the signature {sig:?} of a call: {errors:?}")
        });
    let (formal_inputs, formal_output) = formal_tys.split_at(formal_tys.len() - 1);
    // The arguments that a C-variadic function takes beyond its parameters
    // are inputs that flow nowhere: the callee cannot name their types.
    assert!(
        formal_inputs.len() == query.arg_tys.len()
            || (is_c_variadic(sig) && formal_inputs.len() < query.arg_tys.len()),
        "The call passes {} arguments to a function with signature {sig:?}",
        query.arg_tys.len()
    );

    // The relations the callee may rely on: those that its where clauses and
    // the well-formedness of its signature (normalized or not) and of the
    // header of its impl or trait give (its implied bounds), and those that
    // proving its trait bounds with the impls the trait solver selects gives.
    // Clauses that relate no regions (const arguments, const-ness of impls)
    // are left out.
    let mut obligations: Vec<ty::Predicate<'tcx>> = clauses
        .into_iter()
        .filter(|clause| {
            matches!(
                clause.kind().skip_binder(),
                ty::ClauseKind::Trait(_)
                    | ty::ClauseKind::Projection(_)
                    | ty::ClauseKind::RegionOutlives(_)
                    | ty::ClauseKind::TypeOutlives(_)
            )
        })
        .map(ty::Clause::as_predicate)
        .collect();
    for wf_ty in formal_tys.iter().chain(wf_types) {
        let well_formed = ty::ClauseKind::WellFormed(wf_ty.into());
        obligations.push(ty::Binder::dummy(ty::PredicateKind::Clause(well_formed)).upcast(tcx));
    }
    let solved = solve(&infcx, param_env, obligations);

    let mut resolver = OpportunisticRegionResolver::new(&infcx);
    let mut graph = FlowGraph::new();
    let region_node = |region: ty::Region<'tcx>,
                       resolver: &mut OpportunisticRegionResolver<'_, 'tcx>| {
        Node::Region(region.fold_with(resolver))
    };
    let add_type_outlives = |graph: &mut FlowGraph<'tcx>,
                             resolver: &mut OpportunisticRegionResolver<'_, 'tcx>,
                             ty: ty::Ty<'tcx>,
                             region: ty::Region<'tcx>| {
        // `ty: 'r` holds if each of the components that rustc splits `ty`
        // into outlives `'r`, e.g. only the captures of a closure type.
        let target = region_node(region, resolver);
        for component in outlives_components(ty, tcx) {
            let sources = match component {
                OccurrenceKind::Region(r) => vec![region_node(r, resolver)],
                OccurrenceKind::Opaque(opaque) => {
                    opaque_nodes(opaque.fold_with(resolver), env.for_signature())
                }
                OccurrenceKind::Member(..) => {
                    unreachable!("`outlives_components` reveals no hidden types")
                }
            };
            for source in sources {
                graph.add_flow(source, target);
            }
        }
    };
    for (sup, sub) in &solved.region_outlives {
        let (sup, sub) = (
            region_node(*sup, &mut resolver),
            region_node(*sub, &mut resolver),
        );
        graph.add_flow(sup, sub);
    }
    for (ty, region) in &solved.type_outlives {
        add_type_outlives(&mut graph, &mut resolver, *ty, *region);
    }
    // Bind the projections of the call's arguments and result to the nodes
    // of the instantiated signature, position by position.
    let mut inputs = Vec::new();
    let mut outputs = BTreeSet::new();
    let mut bindings = Vec::new();
    for (i, variadic_ty) in query.arg_tys.iter().enumerate().skip(formal_inputs.len()) {
        let count = extract_generalized_lifetimes(*variadic_ty, env).len();
        inputs.extend((0..count).map(|idx| (ArgIdx::from(i), idx)));
    }
    let bases = query
        .arg_tys
        .iter()
        .zip(formal_inputs)
        .enumerate()
        .map(|(i, (actual, formal))| (ArgIdxOrResult::Argument(i.into()), *actual, *formal))
        .chain(std::iter::once((
            ArgIdxOrResult::Result,
            query.result_ty,
            *formal_output.first().unwrap(),
        )));
    for (base, actual_ty, formal_ty) in bases {
        let lifetimes = extract_generalized_lifetimes(actual_ty, env);
        if let ArgIdxOrResult::Argument(arg) = base {
            inputs.extend((0..lifetimes.len()).map(|idx| (arg, idx)));
        }
        let writable = writable_lifetimes(actual_ty, env);
        let index_of =
            |lifetime: GeneralizedLifetime<'tcx>| lifetimes.iter().position(|l| *l == lifetime);
        for (actual, formal) in aligned_occurrences(actual_ty, formal_ty, tcx) {
            // A region or opaque type at a position that the lifetimes of
            // `actual_ty` do not cover (e.g. in the signature of a closure
            // type) binds nothing: it is a node of the graph only.
            let pairs = paired_lifetimes(actual, formal, env)
                .into_iter()
                .filter_map(|(actual, formal)| {
                    let node = match formal {
                        FormalLifetime::Region(region) => region_node(region, &mut resolver),
                        FormalLifetime::Part(opaque, part) => Node::Opaque(
                            opaque.fold_with(&mut resolver),
                            part.resolve(&mut resolver, tcx),
                        ),
                    };
                    Some((index_of(actual)?, node))
                })
                .collect::<Vec<_>>();
            for (idx, node) in pairs {
                bindings.push(((base, idx), lifetimes.raw[idx], node));
                match base {
                    ArgIdxOrResult::Argument(arg) => {
                        graph.add_flow(Node::Input(arg, idx), node);
                        if writable.contains(&lifetimes.raw[idx]) {
                            graph.add_flow(node, Node::Output(base, idx));
                            outputs.insert((base, idx));
                        }
                    }
                    ArgIdxOrResult::Result => {
                        graph.add_flow(node, Node::Output(base, idx));
                        outputs.insert((base, idx));
                    }
                }
            }
        }
    }

    // The relations a closure body needs, from the borrow checker of the
    // regions given (see `CallSpecQuery::closure_outlives`): at a call of a
    // closure, between the regions of its type; for the closure's own spec,
    // between all regions of its type and of the types of its arguments and
    // result, e.g. from a parameter to a capture.
    let closure_regions: Vec<Vec<(ty::Region<'tcx>, Node<'tcx>)>> = match query.callee {
        Callee::FnDef(def_id, _) if def_id == env.def_id && tcx.is_closure_like(def_id) => {
            let of_type = folder
                .vars
                .iter()
                .map(|(region, var)| (*region, region_node(*var, &mut resolver)));
            let of_arguments = bindings
                .iter()
                .filter_map(|(_, actual, node)| match actual {
                    GeneralizedLifetime::Region(region) => Some((region.rust_region(tcx), *node)),
                    _ => None,
                });
            vec![of_type.chain(of_arguments).collect()]
        }
        _ => folder
            .closures
            .iter()
            .map(|closure| {
                closure
                    .iter()
                    .map(|(region, var)| (*region, region_node(*var, &mut resolver)))
                    .collect()
            })
            .collect(),
    };
    for closure in &closure_regions {
        for &(sup, sup_node) in closure {
            for &(sub, sub_node) in closure {
                if sup != sub && (query.closure_outlives)(sup, sub) {
                    graph.add_flow(sup_node, sub_node);
                }
            }
        }
    }

    // Each part of the value of an opaque type is wired both ways to the
    // lifetime that names it: a region part to the region's node, a
    // `RegionsIn(Q)` part to the node of `Q`'s whole value (see
    // `GeneralizedLifetime`). Wiring may add opaque nodes, which are wired in
    // turn.
    let mut wired = 0;
    while let Some(&node) = graph.nodes.get(wired) {
        wired += 1;
        match node {
            Node::Opaque(_, OpaquePart::Bound(BoundLifetime::Region(region))) => {
                let region = region.rust_region(tcx);
                if !region.is_static() {
                    graph.add_flows_both_ways(node, region_node(region, &mut resolver));
                }
            }
            Node::Opaque(_, OpaquePart::Bound(BoundLifetime::RegionsIn(other))) => {
                graph.add_flows_both_ways(node, Node::Opaque(other.ty(tcx), OpaquePart::Whole));
            }
            _ => {}
        }
    }

    // Two alias types that are equal up to regions are the same type where
    // their regions are equal (see `GeneralizedLifetime`), e.g. in the
    // signature of a closure, whose regions are distinct where its body has
    // equal ones.
    let aliases: Vec<ty::Ty<'tcx>> = graph
        .nodes
        .iter()
        .filter_map(|node| match node {
            Node::Opaque(ty, OpaquePart::Whole) if matches!(ty.kind(), ty::TyKind::Alias(..)) => {
                Some(*ty)
            }
            _ => None,
        })
        .collect();
    for &from in &aliases {
        for &to in &aliases {
            if from == to {
                continue;
            }
            let equal = alias_region_pairs(from, to, tcx).is_some_and(|pairs| {
                pairs.into_iter().all(|(from_region, to_region)| {
                    let (from_node, to_node) = (Node::Region(from_region), Node::Region(to_region));
                    from_region == to_region
                        || (graph.reachable_regions(from_node).contains(&to_node)
                            && graph.reachable_regions(to_node).contains(&from_node))
                })
            });
            if equal {
                graph.add_flow(
                    Node::Opaque(from, OpaquePart::Whole),
                    Node::Opaque(to, OpaquePart::Whole),
                );
            }
        }
    }

    let region_nodes: HashMap<ty::Region<'tcx>, Node<'tcx>> = folder
        .vars
        .iter()
        .map(|(region, var)| (*region, region_node(*var, &mut resolver)))
        .collect();

    // `'static` outlives every region, and every region that the value of an
    // opaque type may hold, as for the flows within a body (see
    // `BorrowCheckerInterface::outlives_generalized`).
    let static_node = Node::Region(tcx.lifetimes.re_static);
    let all_region_nodes: Vec<Node<'tcx>> = graph
        .nodes
        .iter()
        .copied()
        .chain(region_nodes.values().copied())
        .filter(|node| matches!(node, Node::Region(_) | Node::Opaque(..)))
        .collect();
    for node in all_region_nodes {
        graph.add_flow(static_node, node);
    }

    SpecGraph {
        graph,
        inputs,
        outputs,
        region_nodes,
        bindings,
    }
}

/// The spec of a call: the flows from the lifetime projections of its
/// arguments to those of its result and of its arguments after the call.
/// The projections are those of `query.arg_tys` and `query.result_ty` in
/// `query.env`.
#[rustversion::since(2025-05-24)]
#[allow(clippy::unnecessary_wraps)]
pub(crate) fn call_spec(
    query: &CallSpecQuery<'_, '_>,
) -> Result<FunctionShape, MakeFunctionShapeError> {
    let SpecGraph {
        graph,
        mut inputs,
        outputs,
        ..
    } = spec_graph(query);
    inputs.sort_unstable();
    let mut edges = std::collections::HashSet::new();
    for &(arg, idx) in &inputs {
        for output in graph.reachable_outputs(Node::Input(arg, idx)) {
            edges.insert(((arg, idx), output));
        }
    }
    Ok(FunctionShape::from_raw(
        inputs,
        outputs.into_iter().collect(),
        edges,
    ))
}

#[rustversion::before(2025-05-24)]
pub(crate) fn call_spec<'tcx>(
    _query: &CallSpecQuery<'_, 'tcx>,
) -> Result<FunctionShape, MakeFunctionShapeError> {
    Err(MakeFunctionShapeError::UnsupportedRustVersion)
}

/// The flows of the spec of a call that its outlives relations between
/// regions give alone, without going through a part of an opaque type: a flow
/// through a part depends on the impl that the opaque type stands for.
#[rustversion::since(2025-05-24)]
fn flows_through_regions(
    query: &CallSpecQuery<'_, '_>,
) -> HashSet<((ArgIdx, usize), (ArgIdxOrResult, usize))> {
    let spec = spec_graph(query);
    spec.inputs
        .iter()
        .flat_map(|&(arg, idx)| {
            spec.graph
                .outputs_through_regions(Node::Input(arg, idx))
                .into_iter()
                .map(move |output| ((arg, idx), output))
        })
        .collect()
}

#[rustversion::before(2025-05-24)]
fn flows_through_regions(
    _query: &CallSpecQuery<'_, '_>,
) -> HashSet<((ArgIdx, usize), (ArgIdxOrResult, usize))> {
    HashSet::default()
}

/// The spec of the function whose body is analysed, for that body.
struct BodySpec<'tcx> {
    def_id: DefId,
    /// The spec in the lifetime projections of the body's own arguments and
    /// result.
    spec: SpecGraph<'tcx>,
}

/// The spec of the function whose body `ctxt` analyses, or `None` if the body
/// has no signature (a constant, a coroutine) or no rustc borrow checker.
///
/// It is the spec of a call of the function whose arguments and result have
/// the types that the body has for them: the spec in the body's own lifetime
/// projections. For a closure, the callee is the closure type of the body,
/// which has region variables where typeck erased the regions of the
/// closure's type, and the relations that its body needs between them come
/// from the body's region inference (see [`CallSpecQuery::closure_outlives`]).
#[rustversion::since(2025-05-24)]
fn body_spec<'a, 'tcx: 'a>(ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>) -> Option<BodySpec<'tcx>> {
    use crate::rustc_interface::hir::def::DefKind;
    let tcx = ctxt.tcx();
    let body = ctxt.body();
    let def_id = body.source.def_id();
    let arg_tys: Vec<ty::Ty<'tcx>> = body
        .args_iter()
        .map(|local| body.local_decls[local].ty)
        .collect();
    let callee_args = if tcx.is_closure_like(def_id) {
        let ty::TyKind::Closure(_, args) = arg_tys.first()?.peel_refs().kind() else {
            return None;
        };
        args
    } else if matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
        FunctionData::new(def_id).identity_substs(tcx)
    } else {
        return None;
    };
    let region_cx = ctxt.bc().rust_borrow_checker()?.region_infer_ctxt();
    let closure_outlives =
        |sup: ty::Region<'tcx>, sub: ty::Region<'tcx>| match (sup.kind(), sub.kind()) {
            (ty::RegionKind::ReVar(sup), ty::RegionKind::ReVar(sub)) => {
                region_cx.eval_outlives(sup, sub)
            }
            _ => false,
        };
    let spec = spec_graph(&CallSpecQuery {
        callee: Callee::FnDef(def_id, callee_args),
        arg_tys: &arg_tys,
        result_ty: body.local_decls[mir::RETURN_PLACE].ty,
        env: LifetimeEnv::body(tcx, def_id),
        closure_outlives: &closure_outlives,
    });
    Some(BodySpec { def_id, spec })
}

/// Checks the flows into the result that the body `ctxt` analyses has
/// established when it returns, in `graph`, against its spec. Panics (under
/// validity checks) if a lifetime projection of the result is blocked by the
/// projection of an argument that the spec does not let flow into it: the
/// body would hand its caller a loan that its signature does not promise.
///
/// Only the result is checked, not the places that the arguments point to:
/// once an argument is dead, the graph no longer records what flowed into
/// them.
#[rustversion::since(2025-05-24)]
pub(crate) fn check_return_flows<'a, 'tcx: 'a>(
    graph: &BorrowsGraph<'tcx>,
    location: mir::Location,
    ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>,
) {
    let tcx = ctxt.tcx();
    let Some(BodySpec { def_id, spec }) = body_spec(ctxt) else {
        return;
    };
    let mut call_specs: HashMap<mir::Location, CallSpecAt<'tcx>> = HashMap::default();
    let mut flows_into_result: HashSet<((ArgIdx, usize), usize)> = HashSet::default();
    for &(arg, idx) in &spec.inputs {
        for (base, out_idx) in spec.graph.reachable_outputs(Node::Input(arg, idx)) {
            if base == ArgIdxOrResult::Result {
                flows_into_result.insert(((arg, idx), out_idx));
            }
        }
    }

    for node in graph.nodes(ctxt) {
        let PcgNode::LifetimeProjection(projection) = node else {
            continue;
        };
        let Some(MaybeRemoteCurrentPlace::Local(place)) =
            projection.base.maybe_remote_current_place()
        else {
            continue;
        };
        if place.local != mir::RETURN_PLACE || !place.projection.is_empty() {
            continue;
        }
        let result_idx = projection.region_idx.index();
        // The projections of the arguments that the result's projection is
        // blocked by, directly or through other nodes.
        let mut seen: HashSet<PcgNodeWithPlace<'tcx>> = HashSet::from_iter([node]);
        let mut stack = vec![node];
        let mut blocked_inputs = Vec::new();
        while let Some(current) = stack.pop() {
            let Some(local_node) = current.as_local_node() else {
                continue;
            };
            let mut blocked_nodes = Vec::new();
            for edge in graph.edges_blocked_by(local_node, ctxt) {
                let blocked = edge.kind.blocked_nodes(ctxt);
                match call_flows_into(edge.kind, current, &mut call_specs, ctxt) {
                    Some(inputs) => blocked_nodes.extend(blocked.filter(|node| {
                        projection_key(*node).is_some_and(|key| inputs.contains(&key))
                    })),
                    None => blocked_nodes.extend(blocked),
                }
                if let BorrowPcgEdgeKind::Borrow(borrow) = edge.kind {
                    blocked_nodes.extend(reborrowed_references(borrow.blocked_place, ctxt));
                }
            }
            for blocked in blocked_nodes {
                if let PcgNode::LifetimeProjection(blocked_projection) = blocked
                    && let Some(MaybeRemoteCurrentPlace::Remote(remote)) =
                        blocked_projection.base.maybe_remote_current_place()
                {
                    blocked_inputs.push((remote.local, blocked_projection.region_idx.index()));
                } else if matches!(blocked, PcgNode::LifetimeProjection(_)) && seen.insert(blocked)
                {
                    // Loans flow between lifetime projections. The places that
                    // a borrow blocks contribute the references it goes through
                    // (see `reborrowed_references`); their other edges are about
                    // the places' capabilities, not about loans.
                    stack.push(blocked);
                }
            }
        }
        for (local, input_idx) in blocked_inputs {
            let arg = ArgIdx::from(local.as_usize() - 1);
            pcg_validity_assert!(
                flows_into_result.contains(&((arg, input_idx), result_idx)),
                [ctxt at location],
                "Lifetime projection {result_idx} of the result is blocked by lifetime projection \
                 {input_idx} of argument {arg} ({local:?}), but the spec of {} lets no loan flow \
                 from the one into the other",
                tcx.def_path_str(def_id)
            );
        }
    }
}

/// The lifetime projections of the references that a borrow of `place` goes
/// through and whose regions therefore bound the borrow, as rustc's borrow
/// checker relates them: walking from `place` towards its local, each
/// dereferenced reference counts, up to and including the first shared one.
/// For `&**x` with `x: &'s mut &'a u32`, the borrow is bounded by `'a` only:
/// the data behind a shared reference lives as long as that reference.
fn reborrowed_references<'a, 'tcx: 'a>(
    place: MaybeLabelledPlace<'tcx>,
    ctxt: impl HasCompilerCtxt<'a, 'tcx>,
) -> Vec<PcgNodeWithPlace<'tcx>> {
    let mut references = Vec::new();
    let mut prefix = place;
    while let Some((base, elem)) = prefix.last_projection() {
        if elem == mir::ProjectionElem::Deref
            && let ty::TyKind::Ref(_, _, mutability) = base.ty(ctxt).ty.kind()
        {
            // The region of a reference type is its first lifetime.
            let base_node = PlaceOrConst::Place(MaybeRemotePlace::Local(base));
            references.push(PcgNode::LifetimeProjection(LifetimeProjection::from_index(
                base_node,
                0.into(),
            )));
            if mutability.is_not() {
                break;
            }
        }
        prefix = base;
    }
    references
}

/// A lifetime projection of a place, by the place without its label and the
/// index of the lifetime.
fn projection_key(node: PcgNodeWithPlace<'_>) -> Option<(Place<'_>, usize)> {
    let PcgNode::LifetimeProjection(projection) = node else {
        return None;
    };
    let PlaceOrConst::Place(MaybeRemotePlace::Local(place)) = projection.base else {
        return None;
    };
    Some((place.place(), projection.region_idx.index()))
}

/// The spec of a call, with the places of its arguments and result.
struct CallSpecAt<'tcx> {
    edges: HashSet<(FunctionShapeInput, FunctionShapeOutput)>,
    args: Vec<Option<Place<'tcx>>>,
    destination: Place<'tcx>,
}

impl<'tcx> CallSpecAt<'tcx> {
    fn new<'a>(
        location: mir::Location,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>,
    ) -> Self
    where
        'tcx: 'a,
    {
        let terminator = ctxt.body()[location.block].terminator();
        let mir::TerminatorKind::Call {
            func,
            args,
            destination,
            fn_span,
            ..
        } = &terminator.kind
        else {
            panic!("The call edge at {location:?} is not at a call");
        };
        let defined = match func.ty(ctxt.body(), ctxt.tcx()).kind() {
            ty::TyKind::FnDef(def_id, substs) => Some(DefinedFnCall::new(
                FunctionData::new(*def_id),
                fn_def_args(substs),
                ctxt.ctxt().def_id(),
                *fn_span,
            )),
            _ => None,
        };
        let operands: Vec<&mir::Operand<'tcx>> = args.iter().map(|arg| &arg.node).collect();
        let destination: Place<'tcx> = (*destination).into();
        let shape = FunctionCall::new(location, &operands, destination, defined).shape(ctxt);
        Self {
            edges: shape
                .edges()
                .map(|edge| (edge.input, edge.output))
                .collect(),
            args: operands
                .iter()
                .map(|operand| operand.place().map(Into::into))
                .collect(),
            destination,
        }
    }
}

/// If `edge` is the edge of a call, the projections (see [`projection_key`])
/// of its inputs that the call's spec lets flow into its output `output`. A
/// call's edge may couple inputs and outputs that do not flow into each
/// other, so the call's spec says which of them `output` blocks.
fn call_flows_into<'a, 'tcx: 'a>(
    edge: &BorrowPcgEdgeKind<'tcx>,
    output: PcgNodeWithPlace<'tcx>,
    specs: &mut HashMap<mir::Location, CallSpecAt<'tcx>>,
    ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>,
) -> Option<HashSet<(Place<'tcx>, usize)>> {
    let location = match edge {
        BorrowPcgEdgeKind::Coupled(PcgCoupledEdgeKind(FunctionCallOrLoop::FunctionCall(call))) => {
            call.metadata().location()
        }
        BorrowPcgEdgeKind::Abstraction(FunctionCallOrLoop::FunctionCall(call)) => call.location(),
        _ => return None,
    };
    let spec = specs
        .entry(location)
        .or_insert_with(|| CallSpecAt::new(location, ctxt));
    let Some((output_place, output_idx)) = projection_key(output) else {
        return Some(HashSet::default());
    };
    let output_base = if output_place == spec.destination {
        ArgIdxOrResult::Result
    } else {
        let arg = spec
            .args
            .iter()
            .position(|arg| *arg == Some(output_place))?;
        ArgIdxOrResult::Argument(arg.into())
    };
    Some(
        spec.edges
            .iter()
            .filter(|(_, out)| out.base == output_base && out.region_idx.index() == output_idx)
            .filter_map(|(input, _)| {
                spec.args[*input.base].map(|place| (place, input.region_idx.index()))
            })
            .collect(),
    )
}

#[rustversion::before(2025-05-24)]
pub(crate) fn check_return_flows<'a, 'tcx: 'a>(
    _graph: &BorrowsGraph<'tcx>,
    _location: mir::Location,
    _ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>,
) {
}

/// Checks the spec of the function whose body `ctxt` analyses against
/// rustc's borrow checker of that body. Panics (under validity checks) if the
/// outlives relation between the regions of the function's signature that
/// the spec relies on differs from the one that rustc's region inference
/// gives the body's universal regions. If the spec lacked a relation, the
/// body could move a loan its callers do not expect; if it had an extra one,
/// its callers would expect flows that the body cannot perform.
///
/// A closure's spec takes the relations its body needs from the body's
/// region inference (see [`CallSpecQuery::closure_outlives`]), so for a
/// closure the check covers the relations of its signature only.
///
/// Each node of the spec gets the body's region variables for it: those of
/// the regions of the body's arguments and result that are bound to it, and
/// for a lifetime parameter its universal region (see [`BodyRegions`]). The
/// check compares every pair of these, so it also checks the universal
/// regions against the bindings.
#[rustversion::since(2025-05-24)]
pub(crate) fn check_body_spec<'a, 'tcx: 'a>(
    ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>,
) {
    let tcx = ctxt.tcx();
    let Some(BodySpec { def_id, spec }) = body_spec(ctxt) else {
        return;
    };
    let rust_bc = ctxt.bc().rust_borrow_checker().unwrap();
    let region_cx = rust_bc.region_infer_ctxt();
    let body_regions = BodyRegions::new(tcx, def_id);
    let universal_vid = |param: ty::EarlyParamRegion| {
        let vid = body_regions.universal_vid(param);
        assert!(
            rust_bc
                .input_facts()
                .universal_region
                .iter()
                .any(|&universal| ty::RegionVid::from(universal) == vid),
            "The region {vid:?} of {param:?} in the body of {} is not universal",
            tcx.def_path_str(def_id)
        );
        vid
    };
    let mut regions: Vec<(ty::RegionVid, Node<'tcx>)> = spec
        .bindings
        .iter()
        .filter_map(|(_, lifetime, node)| match lifetime {
            GeneralizedLifetime::Region(PcgRegion::RegionVid(vid)) => Some((*vid, *node)),
            _ => None,
        })
        .collect();
    for (region, node) in &spec.region_nodes {
        if let ty::RegionKind::ReEarlyParam(param) = region.kind() {
            regions.push((universal_vid(param), *node));
        }
    }
    for node in &spec.graph.nodes {
        if let Node::Region(region) = node
            && let ty::RegionKind::ReEarlyParam(param) = region.kind()
        {
            regions.push((universal_vid(param), *node));
        }
    }
    for &(sup_vid, sup) in &regions {
        let reachable = spec.graph.reachable_regions(sup);
        for &(sub_vid, sub) in &regions {
            if sup_vid == sub_vid {
                continue;
            }
            let in_spec = reachable.contains(&sub);
            let in_rustc = region_cx.eval_outlives(sup_vid, sub_vid);
            pcg_validity_assert!(
                in_spec == in_rustc,
                [ctxt],
                "The spec of {} {} that {sup_vid:?} ({sup:?}) outlives {sub_vid:?} ({sub:?}), but \
                 rustc's region inference of its body {}",
                tcx.def_path_str(def_id),
                if in_spec {
                    "assumes"
                } else {
                    "does not assume"
                },
                if in_rustc { "does" } else { "does not" },
            );
        }
    }
}

#[rustversion::before(2025-05-24)]
pub(crate) fn check_body_spec<'a, 'tcx: 'a>(
    _ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>,
) {
}

/// Checks the spec `shape` of the call at `location`, computed from `query`,
/// against rustc's borrow checker. Panics (under validity checks) if
///
/// - the constraints that the borrow checker generated for this call relate
///   the region of an input to the region of an output, but the spec has no
///   edge between them: the spec misses a flow that rustc's typing of the
///   call allows (completeness); or
/// - the spec has an edge between two regions, by the outlives relations
///   between regions alone, that the borrow checker does not let outlive one
///   another at the call: the edge has no reason in rustc (justification).
///   A flow through a part of an opaque type of the caller is not checked:
///   it depends on the impl that the type stands for, and rustc relates the
///   two regions only where it knows that impl.
///
/// The constraints of the call are those at its location that do not hold
/// at every location: subtyping of the arguments and the result, the
/// well-formedness of the instantiated signature, and the callee's bounds.
/// Closure requirements, which rustc applies where the closure is created,
/// are not among them; the completeness check is weaker for closures.
pub(crate) fn check_call_spec<'a, 'tcx: 'a>(
    shape: &FunctionShape,
    query: &CallSpecQuery<'_, 'tcx>,
    location: mir::Location,
    ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>,
) {
    let Some(rust_borrow_checker) = ctxt.bc().rust_borrow_checker() else {
        return;
    };
    let region_flows = flows_through_regions(query);
    let env = ctxt.lifetime_env();
    let lifetime_of = |base: ArgIdxOrResult, idx: usize| -> GeneralizedLifetime<'tcx> {
        let ty = match base {
            ArgIdxOrResult::Argument(arg) => query.arg_tys[*arg],
            ArgIdxOrResult::Result => query.result_ty,
        };
        extract_generalized_lifetimes(ty, env).raw[idx]
    };
    // The region variable a lifetime of the call stands for, if it is known:
    // its region, or the region of an alias type's argument that names a
    // part of the alias's value.
    let region_of = |lifetime: GeneralizedLifetime<'tcx>| -> Option<ty::RegionVid> {
        match lifetime {
            GeneralizedLifetime::Region(PcgRegion::RegionVid(vid))
            | GeneralizedLifetime::BoundPart(
                OpaqueTy::Alias(_),
                BoundLifetime::Region(PcgRegion::RegionVid(vid)),
            ) => Some(vid),
            _ => None,
        }
    };

    let location_table = rust_borrow_checker.location_table();
    let facts = rust_borrow_checker.input_facts();
    let mid = location_table.mid_index(location);
    let start = location_table.start_index(location);
    let everywhere: HashSet<(ty::RegionVid, ty::RegionVid)> = facts
        .subset_base
        .iter()
        .filter(|(_, _, point)| *point == start)
        .map(|(sup, sub, _)| ((*sup).into(), (*sub).into()))
        .collect();
    let mut successors: HashMap<ty::RegionVid, Vec<ty::RegionVid>> = HashMap::default();
    for (sup, sub, point) in &facts.subset_base {
        let pair: (ty::RegionVid, ty::RegionVid) = ((*sup).into(), (*sub).into());
        if *point == mid && !everywhere.contains(&pair) {
            successors.entry(pair.0).or_default().push(pair.1);
        }
    }
    let reachable_from = |vid: ty::RegionVid| -> HashSet<ty::RegionVid> {
        let mut seen: HashSet<ty::RegionVid> = HashSet::from_iter([vid]);
        let mut stack = vec![vid];
        while let Some(current) = stack.pop() {
            for next in successors.get(&current).into_iter().flatten() {
                if seen.insert(*next) {
                    stack.push(*next);
                }
            }
        }
        seen
    };

    let edges: HashSet<(FunctionShapeInput, FunctionShapeOutput)> = shape
        .edges()
        .map(|edge| (edge.input, edge.output))
        .collect();
    for input in &shape.inputs {
        let in_lifetime = lifetime_of(
            ArgIdxOrResult::Argument(input.base),
            input.region_idx.index(),
        );
        let reachable: HashSet<ty::RegionVid> = region_of(in_lifetime)
            .map(reachable_from)
            .unwrap_or_default();
        for output in &shape.outputs {
            let out_lifetime = lifetime_of(output.base, output.region_idx.index());
            let has_edge = edges.contains(&(*input, *output));
            pcg_validity_assert!(
                has_edge || !region_of(out_lifetime).is_some_and(|vid| reachable.contains(&vid)),
                [ctxt at location],
                "The spec of the call misses a flow from {in_lifetime:?} of argument {} to \
                 {out_lifetime:?} of {} that rustc's constraints for the call allow",
                input.base,
                output.base
            );
            if region_flows.contains(&(
                (input.base, input.region_idx.index()),
                (output.base, output.region_idx.index()),
            )) && let GeneralizedLifetime::Region(in_region) = in_lifetime
                && let GeneralizedLifetime::Region(out_region) = out_lifetime
            {
                pcg_validity_assert!(
                    ctxt.bc().outlives(in_region, out_region, location),
                    [ctxt at location],
                    "The spec of the call has a flow from {in_lifetime:?} of argument {} to \
                     {out_lifetime:?} of {}, but rustc does not let the first outlive the second",
                    input.base,
                    output.base
                );
            }
        }
    }
}

/// The regions and opaque types that rustc requires to outlive a region for
/// `ty` to outlive it (see `push_outlives_components`).
fn outlives_components<'tcx>(ty: ty::Ty<'tcx>, tcx: ty::TyCtxt<'tcx>) -> Vec<OccurrenceKind<'tcx>> {
    use crate::rustc_interface::middle::ty::outlives::{Component, push_outlives_components};
    fn flatten<'tcx>(
        components: impl IntoIterator<Item = Component<ty::TyCtxt<'tcx>>>,
        tcx: ty::TyCtxt<'tcx>,
        out: &mut Vec<OccurrenceKind<'tcx>>,
    ) {
        for component in components {
            match component {
                Component::Region(region) => out.push(OccurrenceKind::Region(region)),
                Component::Param(param) => {
                    out.push(OccurrenceKind::Opaque(ty::Ty::new_param(
                        tcx,
                        param.index,
                        param.name,
                    )));
                }
                Component::EscapingAlias(components) => flatten(components, tcx, out),
                Component::Placeholder(_) | Component::UnresolvedInferenceVariable(_) => {}
                alias => out.push(OccurrenceKind::Opaque(alias_ty(&alias, tcx))),
            }
        }
    }
    // The vector type is the one of rustc's `smallvec`, which is inferred.
    #[allow(clippy::default_trait_access)]
    let mut components = Default::default();
    push_outlives_components(tcx, ty, &mut components);
    let mut out = Vec::new();
    flatten(components, tcx, &mut out);
    out
}

/// The type of an alias component of an outlives obligation.
#[rustversion::since(2026-08-01)]
fn alias_ty<'tcx>(
    component: &ty::outlives::Component<ty::TyCtxt<'tcx>>,
    tcx: ty::TyCtxt<'tcx>,
) -> ty::Ty<'tcx> {
    use crate::rustc_interface::middle::ty::outlives::Component;
    let Component::Alias(is_rigid, alias) = component else {
        unreachable!("{component:?} is not an alias component")
    };
    alias.to_ty(tcx, *is_rigid)
}

/// The type of an alias component of an outlives obligation.
#[rustversion::before(2026-08-01)]
fn alias_ty<'tcx>(
    component: &ty::outlives::Component<ty::TyCtxt<'tcx>>,
    tcx: ty::TyCtxt<'tcx>,
) -> ty::Ty<'tcx> {
    use crate::rustc_interface::middle::ty::outlives::Component;
    let Component::Alias(alias) = component else {
        unreachable!("{component:?} is not an alias component")
    };
    alias.to_ty(tcx)
}

/// The nodes for the lifetimes of the opaque type `opaque` in `env`.
fn opaque_nodes<'tcx>(opaque: ty::Ty<'tcx>, env: LifetimeEnv<'tcx>) -> Vec<Node<'tcx>> {
    let parts = OpaqueTy::try_from(opaque)
        .map(|opaque_ty| env.bound_lifetimes(opaque_ty))
        .unwrap_or_default();
    std::iter::once(OpaquePart::Whole)
        .chain(parts.into_iter().map(OpaquePart::Bound))
        .map(|part| Node::Opaque(opaque, part))
        .collect()
}
