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
            ArgIdx, ArgIdxOrResult, FunctionData, FunctionShape, FunctionShapeInput,
            FunctionShapeOutput, MakeFunctionShapeError,
        },
        region_projection::PcgRegion,
        visitor::{
            BoundLifetime, GeneralizedLifetime, LifetimeEnv, OpaqueTy,
            extract_generalized_lifetimes,
        },
    },
    pcg_validity_assert,
    rustc_interface::{
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
        HasBorrowCheckerCtxt, HasLifetimeEnv,
        data_structures::{HashMap, HashSet},
        normalize::deeply_normalize,
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
    /// closure type in `env`.
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
    /// bound parts.
    Opaque(ty::Ty<'tcx>, OpaquePart<'tcx>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum OpaquePart<'tcx> {
    /// All of the value: `RegionsIn` of the opaque type.
    Whole,
    /// A bound part of the value.
    Bound(BoundLifetime<'tcx>),
    /// What is written into the value of an alias type (see
    /// [`Node::written`]).
    Written,
}

impl Node<'_> {
    /// The node that the loans flowing into `self` go to. For the value of an
    /// alias type, which is made of the regions of its arguments, these are
    /// kept apart from the loans read from it, so that a loan cannot enter
    /// the value through one region and leave it through another.
    fn written(self) -> Self {
        match self {
            Node::Opaque(ty, OpaquePart::Whole) if matches!(ty.kind(), ty::TyKind::Alias(..)) => {
                Node::Opaque(ty, OpaquePart::Written)
            }
            other => other,
        }
    }
}

/// A region or an opaque type at one position of a type, and whether the
/// callee can write into it when the type is the type of an argument.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Occurrence<'tcx> {
    pub(crate) kind: OccurrenceKind<'tcx>,
    pub(crate) writable: bool,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum OccurrenceKind<'tcx> {
    Region(ty::Region<'tcx>),
    /// A type parameter or an alias type.
    Opaque(ty::Ty<'tcx>),
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
pub(crate) fn occurrences<'tcx>(ty: ty::Ty<'tcx>, tcx: ty::TyCtxt<'tcx>) -> Vec<Occurrence<'tcx>> {
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
            (GenericArgKind::Lifetime(actual_region), GenericArgKind::Lifetime(formal_region)) => {
                let bound =
                    |region: ty::Region<'tcx>| matches!(region.kind(), ty::RegionKind::ReBound(..));
                match (bound(actual_region), bound(formal_region)) {
                    (false, false) => pairs.push((
                        OccurrenceKind::Region(actual_region),
                        OccurrenceKind::Region(formal_region),
                    )),
                    (true, true) => {}
                    _ => mismatch(),
                }
            }
            (GenericArgKind::Const(_), GenericArgKind::Const(_)) => {}
            _ => mismatch(),
        }
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
        if !matches!(region.kind(), ty::RegionKind::ReBound(..)) {
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
            ty::RegionKind::ReBound(..) | ty::RegionKind::ReStatic => region,
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
    take_region_assumptions(infcx);
    SolvedRelations {
        region_outlives: region_outlives(infcx),
        type_outlives,
    }
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

fn take_region_assumptions(infcx: &InferCtxt<'_>) {
    infcx.take_registered_region_assumptions();
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
) -> (ty::FnSig<'tcx>, Vec<ty::Clause<'tcx>>) {
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
            (sig, clauses)
        }
        Callee::FnPtr(poly_sig) => {
            let sig = tcx
                .instantiate_bound_regions(poly_sig, |_| folder.fresh_var())
                .0
                .fold_with(folder);
            (sig, Vec::new())
        }
    }
}

/// The spec of a call: the flows from the lifetime projections of its
/// arguments to those of its result and of its arguments after the call.
/// The projections are those of `query.arg_tys` and `query.result_ty` in
/// `query.env`.
#[rustversion::since(2025-05-24)]
#[allow(clippy::unnecessary_wraps)]
pub(crate) fn call_spec<'tcx>(
    query: &CallSpecQuery<'_, 'tcx>,
) -> Result<FunctionShape, MakeFunctionShapeError> {
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
    let (sig, clauses) = instantiate_callee(query.callee, &mut folder);
    let formal_tys =
        deeply_normalize(&infcx, param_env, sig.inputs_and_output).unwrap_or_else(|errors| {
            panic!("Cannot normalize the signature {sig:?} of a call: {errors:?}")
        });
    let (formal_inputs, formal_output) = formal_tys.split_at(formal_tys.len() - 1);
    assert_eq!(
        formal_inputs.len(),
        query.arg_tys.len(),
        "The call passes {} arguments to a function with signature {sig:?}",
        query.arg_tys.len()
    );

    // The relations the callee may rely on: those that its where clauses and
    // the well-formedness of its signature give, and those that proving its
    // trait bounds with the impls the trait solver selects gives. Clauses
    // that relate no regions (const arguments, const-ness of impls) are left
    // out.
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
    for formal_ty in formal_tys {
        let well_formed = ty::ClauseKind::WellFormed(formal_ty.into());
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
        let target = region_node(region, resolver);
        for occurrence in occurrences(ty, tcx) {
            let sources = match occurrence.kind {
                OccurrenceKind::Region(r) => vec![region_node(r, resolver)],
                OccurrenceKind::Opaque(opaque) => opaque_nodes(opaque.fold_with(resolver), env),
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
    for closure in &folder.closures {
        for (sup, sup_var) in closure {
            for (sub, sub_var) in closure {
                if sup != sub && (query.closure_outlives)(*sup, *sub) {
                    graph.add_flow(
                        region_node(*sup_var, &mut resolver),
                        region_node(*sub_var, &mut resolver),
                    );
                }
            }
        }
    }

    // Bind the projections of the call's arguments and result to the nodes
    // of the instantiated signature, position by position.
    let mut inputs = Vec::new();
    let mut outputs = BTreeSet::new();
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
            let bindings: Vec<(usize, Node<'tcx>)> = match (actual, formal) {
                (OccurrenceKind::Region(actual), OccurrenceKind::Region(formal)) => {
                    index_of(GeneralizedLifetime::Region(actual.into()))
                        .map(|idx| (idx, region_node(formal, &mut resolver)))
                        .into_iter()
                        .collect()
                }
                (OccurrenceKind::Region(actual), OccurrenceKind::Opaque(formal)) => {
                    index_of(GeneralizedLifetime::Region(actual.into()))
                        .map(|idx| {
                            let formal = formal.fold_with(&mut resolver);
                            (idx, Node::Opaque(formal, OpaquePart::Whole))
                        })
                        .into_iter()
                        .collect()
                }
                (OccurrenceKind::Opaque(actual), OccurrenceKind::Region(formal)) => {
                    let actual = OpaqueTy::try_from(actual).unwrap();
                    index_of(GeneralizedLifetime::RegionsIn(actual))
                        .map(|idx| (idx, region_node(formal, &mut resolver)))
                        .into_iter()
                        .collect()
                }
                (OccurrenceKind::Opaque(actual), OccurrenceKind::Opaque(formal)) => {
                    let actual = OpaqueTy::try_from(actual).unwrap();
                    let formal = formal.fold_with(&mut resolver);
                    std::iter::once(OpaquePart::Whole)
                        .chain(
                            env.bound_lifetimes(actual)
                                .into_iter()
                                .map(OpaquePart::Bound),
                        )
                        .filter_map(|part| {
                            let lifetime = match part {
                                OpaquePart::Whole => GeneralizedLifetime::RegionsIn(actual),
                                OpaquePart::Bound(l) => GeneralizedLifetime::BoundPart(actual, l),
                                OpaquePart::Written => unreachable!(),
                            };
                            Some((index_of(lifetime)?, Node::Opaque(formal, part)))
                        })
                        .collect()
                }
            };
            for (idx, node) in bindings {
                match base {
                    ArgIdxOrResult::Argument(arg) => {
                        graph.add_flow(Node::Input(arg, idx), node);
                        if writable.contains(&lifetimes.raw[idx]) {
                            graph.add_flow(node.written(), Node::Output(base, idx));
                            outputs.insert((base, idx));
                        }
                    }
                    ArgIdxOrResult::Result => {
                        graph.add_flow(node.written(), Node::Output(base, idx));
                        outputs.insert((base, idx));
                    }
                }
            }
        }
    }

    // The lifetimes of opaque types: a bound part relates to the lifetime
    // its bound names, an alias to the lifetimes of its arguments. The value
    // of an alias holds loans of the regions of its arguments; a loan that
    // enters it through one of them leaves it through that same one, so it
    // has a node for what is read from it and one for what is written to it.
    let opaque_nodes_in_graph: Vec<Node<'tcx>> = graph
        .nodes
        .iter()
        .copied()
        .filter(|node| matches!(node, Node::Opaque(..)))
        .collect();
    for node in opaque_nodes_in_graph {
        let Node::Opaque(opaque, part) = node else {
            unreachable!()
        };
        match part {
            OpaquePart::Bound(BoundLifetime::Region(region)) => {
                let region = region.rust_region(tcx);
                if !region.is_static() {
                    graph.add_flows_both_ways(node, region_node(region, &mut resolver));
                }
            }
            OpaquePart::Bound(BoundLifetime::RegionsIn(other)) => {
                graph.add_flows_both_ways(node, Node::Opaque(other.ty(tcx), OpaquePart::Whole));
            }
            OpaquePart::Whole | OpaquePart::Written => {
                if let ty::TyKind::Alias(_, alias) = opaque.kind() {
                    let read = Node::Opaque(opaque, OpaquePart::Whole);
                    let written = read.written();
                    graph.add_flow(read, written);
                    for arg in alias.args {
                        for member in member_nodes(arg, tcx, env, &mut resolver) {
                            graph.add_flow(read, member);
                            graph.add_flow(member, written);
                        }
                    }
                }
            }
        }
    }

    // `'static` outlives every region.
    let static_node = Node::Region(tcx.lifetimes.re_static);
    let region_nodes: Vec<Node<'tcx>> = graph
        .nodes
        .iter()
        .copied()
        .filter(|node| matches!(node, Node::Region(_)))
        .collect();
    for node in region_nodes {
        graph.add_flow(static_node, node);
    }

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

/// Checks the spec `shape` of the call at `location`, whose arguments and
/// result have the types `arg_tys` and `result_ty`, against rustc's borrow
/// checker. Panics (under validity checks) if
///
/// - the constraints that the borrow checker generated for this call relate
///   the region of an input to the region of an output, but the spec has no
///   edge between them: the spec misses a flow that rustc's typing of the
///   call allows (completeness); or
/// - the spec has an edge between two regions that the borrow checker does
///   not let outlive one another at the call: the edge has no reason in
///   rustc (justification).
///
/// The constraints of the call are those at its location that do not hold
/// at every location: subtyping of the arguments and the result, the
/// well-formedness of the instantiated signature, and the callee's bounds.
/// Closure requirements, which rustc applies where the closure is created,
/// are not among them; the completeness check is weaker for closures.
pub(crate) fn check_call_spec<'a, 'tcx: 'a>(
    shape: &FunctionShape,
    arg_tys: &[ty::Ty<'tcx>],
    result_ty: ty::Ty<'tcx>,
    location: mir::Location,
    ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>,
) {
    let env = ctxt.lifetime_env();
    let lifetime_of = |base: ArgIdxOrResult, idx: usize| -> GeneralizedLifetime<'tcx> {
        let ty = match base {
            ArgIdxOrResult::Argument(arg) => arg_tys[*arg],
            ArgIdxOrResult::Result => result_ty,
        };
        extract_generalized_lifetimes(ty, env).raw[idx]
    };
    // The region variables a lifetime of the call stands for, if they are
    // known: its region, or the regions of an alias type's arguments, whose
    // value holds loans of these.
    let regions_of = |lifetime: GeneralizedLifetime<'tcx>| -> Vec<ty::RegionVid> {
        let mut vids = Vec::new();
        match lifetime {
            GeneralizedLifetime::Region(PcgRegion::RegionVid(vid)) => vids.push(vid),
            GeneralizedLifetime::RegionsIn(OpaqueTy::Alias(alias)) => {
                ctxt.tcx().for_each_free_region(&alias, |region| {
                    if let ty::RegionKind::ReVar(vid) = region.kind() {
                        vids.push(vid);
                    }
                });
            }
            _ => {}
        }
        vids
    };

    let Some(rust_borrow_checker) = ctxt.bc().rust_borrow_checker() else {
        return;
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
        let in_regions = regions_of(in_lifetime);
        let reachable: HashSet<ty::RegionVid> = in_regions
            .iter()
            .flat_map(|vid| reachable_from(*vid))
            .collect();
        for output in &shape.outputs {
            let out_lifetime = lifetime_of(output.base, output.region_idx.index());
            let out_regions = regions_of(out_lifetime);
            let has_edge = edges.contains(&(*input, *output));
            pcg_validity_assert!(
                has_edge || !out_regions.iter().any(|vid| reachable.contains(vid)),
                [ctxt at location],
                "The spec of the call misses a flow from {in_lifetime:?} of argument {} to \
                 {out_lifetime:?} of {} that rustc's constraints for the call allow",
                input.base,
                output.base
            );
            if has_edge
                && let GeneralizedLifetime::Region(in_region) = in_lifetime
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

/// The nodes for the lifetimes of a generic argument of an alias type.
fn member_nodes<'tcx>(
    arg: ty::GenericArg<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    env: LifetimeEnv<'tcx>,
    resolver: &mut OpportunisticRegionResolver<'_, 'tcx>,
) -> Vec<Node<'tcx>> {
    if let Some(region) = arg.as_region() {
        return if region.is_static() || matches!(region.kind(), ty::RegionKind::ReBound(..)) {
            vec![]
        } else {
            vec![Node::Region(region.fold_with(resolver))]
        };
    }
    let Some(ty) = arg.as_type() else {
        return vec![];
    };
    occurrences(ty, tcx)
        .into_iter()
        .flat_map(|occurrence| match occurrence.kind {
            OccurrenceKind::Region(region) if !region.is_static() => {
                vec![Node::Region(region.fold_with(resolver))]
            }
            OccurrenceKind::Region(_) => vec![],
            OccurrenceKind::Opaque(opaque) => opaque_nodes(opaque.fold_with(resolver), env),
        })
        .collect()
}
