use derive_more::From;
use std::hash::Hash;

use crate::{
    borrow_pcg::{
        abstraction::body_regions::BodyRegions, region_projection::region_is_invariant_in_type,
    },
    rustc_interface::{
        hir::def_id::DefId,
        index::IndexVec,
        middle::ty::{self, TypeSuperVisitable, TypeVisitable, TypeVisitor},
    },
    utils::{
        HasTyCtxt,
        display::{DisplayCtxtFor, DisplayOutput, DisplayWithCtxt, OutputMode},
    },
};

use super::region_projection::{Generalized, LifetimeProjectionIdx, PcgRegion, Region};

/// Trait abstracting over lifetimes
///
/// Implementors define which "lifetime-like" values are extracted from a type
/// and which [`LifetimeProjectionIdx`] kind they correspond to. The two
/// implementations are:
///
/// - [`PcgRegion`]: extracts concrete regions (lifetime projections).
/// - [`GeneralizedLifetime`]: extracts regions *and* `RegionsIn(τ)` for opaque
///   types (generalized lifetime projections).
pub trait LifetimeKind<'tcx>: Sized + Copy + PartialEq + Eq + std::fmt::Debug + Hash {
    /// The index kind: [`Region`] for lifetime projections, [`Generalized`]
    /// for generalized lifetime projections.
    type IdxMarker: super::region_projection::RegionIdxMarker;
}

pub(crate) trait LifetimeDataCtxt<'tcx, Kind: LifetimeKind<'tcx>> {
    /// Whether this lifetime appears in an invariant (mutable) position in `ty`.
    fn is_invariant_in_type(&self, kind: Kind, ty: ty::Ty<'tcx>) -> bool;
}

impl<'tcx> LifetimeKind<'tcx> for PcgRegion<'tcx> {
    type IdxMarker = Region;
}

impl<'tcx, Ctxt: Copy + HasTyCtxt<'tcx>> LifetimeDataCtxt<'tcx, PcgRegion<'tcx>> for Ctxt {
    fn is_invariant_in_type(&self, kind: PcgRegion<'tcx>, ty: ty::Ty<'tcx>) -> bool {
        region_is_invariant_in_type(self.tcx(), kind, ty)
    }
}

impl<'tcx> LifetimeKind<'tcx> for GeneralizedLifetime<'tcx> {
    type IdxMarker = Generalized;
}

impl<'tcx> From<ty::Region<'tcx>> for GeneralizedLifetime<'tcx> {
    fn from(region: ty::Region<'tcx>) -> GeneralizedLifetime<'tcx> {
        GeneralizedLifetime::Region(region.into())
    }
}

impl<'tcx, Ctxt: Copy + HasTyCtxt<'tcx>> LifetimeDataCtxt<'tcx, GeneralizedLifetime<'tcx>>
    for Ctxt
{
    fn is_invariant_in_type(&self, kind: GeneralizedLifetime<'tcx>, ty: ty::Ty<'tcx>) -> bool {
        match kind {
            GeneralizedLifetime::Region(region) => self.is_invariant_in_type(region, ty),
            // A type parameter `T` that appears in the type is always
            // considered invariant — any borrows hidden inside could be
            // affected by the function.
            GeneralizedLifetime::RegionsIn(_) | GeneralizedLifetime::BoundPart(..) => true,
        }
    }
}

/// Whether `region` is bound by a binder (`ReBound`) that a visitor of the
/// type it occurs in has entered, e.g. the `'x` of `dyn for<'x> Fn(&'x u8)`.
/// Such a region names no data that the type's value borrows: it is chosen
/// anew at each use.
pub(crate) fn is_bound_region(region: ty::Region<'_>) -> bool {
    matches!(region.kind(), ty::RegionKind::ReBound(..))
}

/// Whether the region argument `region` of an alias type names a part of its
/// value (see [`LifetimeEnv::member_lifetimes`]): `'static`, bound and erased
/// regions (as in the signature of a closure type) name no data.
pub(crate) fn names_part(region: ty::Region<'_>) -> bool {
    !region.is_static() && !is_bound_region(region) && !region.is_erased()
}

struct LifetimeExtractor<'tcx> {
    lifetimes: Vec<ty::Region<'tcx>>,
}

impl<'tcx> TypeVisitor<ty::TyCtxt<'tcx>> for LifetimeExtractor<'tcx> {
    fn visit_ty(&mut self, ty: ty::Ty<'tcx>) {
        match ty.kind() {
            // The value behind a `dyn Sink<'b> + 'd` may hold borrows of both
            // `'d` and `'b`: the object's methods can store a `&'b String`
            // into it. The region bound comes first, then the free regions
            // of the trait and its associated type bindings.
            ty::TyKind::Dynamic(predicates, region, ..) => {
                self.visit_region(*region);
                predicates.visit_with(self);
            }
            // A function pointer or a function item is code, not data: its
            // value holds no borrows. Its regions are those of the function's
            // signature, which may be contravariant.
            ty::TyKind::FnPtr(_, _) | ty::TyKind::FnDef(..) => {}
            ty::TyKind::Closure(_, args) => {
                let closure_args = args.as_closure();
                let upvar_tys = closure_args.upvar_tys();
                for ty in upvar_tys {
                    self.visit_ty(ty);
                }
            }
            _ => {
                ty.super_visit_with(self);
            }
        }
    }
    fn visit_region(&mut self, rr: ty::Region<'tcx>) {
        if !is_bound_region(rr) && !self.lifetimes.contains(&rr) {
            self.lifetimes.push(rr);
        }
    }
}

/// Returns all of the (possibly nested) regions in `ty` that could be part of
/// its region projection. In particular, the intention of this function is to
/// *only* return regions that correspond to data borrowed in a type. In
/// particular, for closures / functions, we do not include regions in the input
/// or argument types.
/// If this type is a reference type, e.g. `&'a mut T`, then this will return
/// `'a` and the regions within `T`.
///
/// The resulting list does not contain duplicates, e.g. T<'a, 'a> will return
/// `['a]`. Note that the order of the returned regions is arbitrary, but
/// consistent between calls to types with the same "shape". E.g T<'a, 'b> and
/// T<'c, 'd> will return `['a, 'b]` and `['c, 'd]` respectively. This enables
/// substitution of regions to handle moves in the PCG e.g for the statement
/// `let x: T<'a, 'b> = move c: T<'c, 'd>`.
pub(crate) fn extract_regions(
    ty: ty::Ty<'_>,
) -> IndexVec<LifetimeProjectionIdx<Region>, PcgRegion<'_>> {
    let mut visitor = LifetimeExtractor { lifetimes: vec![] };
    ty.visit_with(&mut visitor);
    visitor.lifetimes.iter().map(|r| (*r).into()).collect()
}

/// `ty` with all regions erased and bound regions anonymized.
#[rustversion::since(2025-12-01)]
pub(crate) fn erase_regions<'tcx>(ty: ty::Ty<'tcx>, tcx: ty::TyCtxt<'tcx>) -> ty::Ty<'tcx> {
    tcx.erase_and_anonymize_regions(ty)
}

/// `ty` with all regions erased and bound regions anonymized.
#[rustversion::before(2025-12-01)]
pub(crate) fn erase_regions<'tcx>(ty: ty::Ty<'tcx>, tcx: ty::TyCtxt<'tcx>) -> ty::Ty<'tcx> {
    tcx.erase_regions(ty)
}

/// The definition and arguments of `ty`, if it is an alias type.
#[rustversion::since(2026-08-01)]
pub(crate) fn alias_def(ty: ty::Ty<'_>) -> Option<(DefId, ty::GenericArgsRef<'_>)> {
    let ty::TyKind::Alias(_, alias) = ty.kind() else {
        return None;
    };
    let def_id = match alias.kind {
        ty::AliasTyKind::Projection { def_id }
        | ty::AliasTyKind::Inherent { def_id }
        | ty::AliasTyKind::Opaque { def_id }
        | ty::AliasTyKind::Free { def_id } => def_id,
    };
    Some((def_id, alias.args))
}

/// The definition and arguments of `ty`, if it is an alias type.
#[rustversion::before(2026-08-01)]
pub(crate) fn alias_def(ty: ty::Ty<'_>) -> Option<(DefId, ty::GenericArgsRef<'_>)> {
    let ty::TyKind::Alias(_, alias) = ty.kind() else {
        return None;
    };
    Some((alias.def_id, alias.args))
}

/// If the types `a` and `b` are equal up to regions, their regions paired by
/// position: they are the same type where each pair is equal (see
/// [`GeneralizedLifetime`]). Erased regions have positions too.
pub(crate) fn alias_region_pairs<'tcx>(
    a: ty::Ty<'tcx>,
    b: ty::Ty<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
) -> Option<Vec<(ty::Region<'tcx>, ty::Region<'tcx>)>> {
    if erase_regions(a, tcx) != erase_regions(b, tcx) {
        return None;
    }
    let regions = |ty: ty::Ty<'tcx>| {
        let mut regions = Vec::new();
        ty::fold_regions(tcx, ty, |region, _| {
            regions.push(region);
            region
        });
        regions
    };
    Some(regions(a).into_iter().zip(regions(b)).collect())
}

/// An opaque type whose internal structure is not visible for lifetime
/// extraction: either a type parameter (`T`, `Self`) or a non-normalizable
/// associated type (`<Self as Deref>::Target`).
#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum OpaqueTy<'tcx> {
    /// A type parameter (e.g., `T`, `Self`).
    Param(ty::ParamTy),
    /// A non-normalizable alias type (e.g., `<Self as Deref>::Target`).
    Alias(ty::Ty<'tcx>),
}

impl<'tcx> TryFrom<ty::Ty<'tcx>> for OpaqueTy<'tcx> {
    type Error = ();

    fn try_from(ty: ty::Ty<'tcx>) -> Result<Self, Self::Error> {
        match ty.kind() {
            ty::TyKind::Param(param_ty) => Ok(Self::Param(*param_ty)),
            ty::TyKind::Alias(..) => Ok(Self::Alias(ty)),
            _ => Err(()),
        }
    }
}

impl<'tcx> OpaqueTy<'tcx> {
    /// Returns the underlying type as a `ty::Ty`.
    pub fn ty(self, tcx: ty::TyCtxt<'tcx>) -> ty::Ty<'tcx> {
        match self {
            Self::Param(param_ty) => ty::Ty::new_param(tcx, param_ty.index, param_ty.name),
            Self::Alias(alias_ty) => alias_ty,
        }
    }

    /// Returns `true` if this is a type parameter.
    pub fn is_param(self) -> bool {
        matches!(self, Self::Param(_))
    }
}

impl std::fmt::Display for OpaqueTy<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Param(param_ty) => write!(f, "{}", param_ty.name),
            Self::Alias(alias_ty) => write!(f, "{alias_ty}"),
        }
    }
}

/// A lifetime that a bound on an opaque type mentions: a region, or the
/// lifetimes of an opaque type, e.g. `'c` in `T: Sink<'c>`, `RegionsIn(A)` in
/// `Self: Extend<A>`, and `'a` in `I: Iterator<Item = &'a u8>`.
#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum BoundLifetime<'tcx> {
    Region(PcgRegion<'tcx>),
    RegionsIn(OpaqueTy<'tcx>),
}

impl std::fmt::Display for BoundLifetime<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Region(region) => write!(f, "{region:?}"),
            Self::RegionsIn(opaque_ty) => write!(f, "RegionsIn({opaque_ty})"),
        }
    }
}

impl<'tcx> From<BoundLifetime<'tcx>> for GeneralizedLifetime<'tcx> {
    fn from(lifetime: BoundLifetime<'tcx>) -> Self {
        match lifetime {
            BoundLifetime::Region(region) => GeneralizedLifetime::Region(region),
            BoundLifetime::RegionsIn(opaque) => GeneralizedLifetime::RegionsIn(opaque),
        }
    }
}

/// A generalized lifetime: a region, `RegionsIn(τ)` for an opaque type (type
/// parameter or non-normalizable alias), or a part of an opaque type that its
/// bounds name.
///
/// Loans flow between generalized lifetimes by these rules, which both the
/// flows within a body ([`outlives_generalized`]) and the spec of a call
/// follow, each with its own relation between regions (rustc's region
/// inference of the body, or what the callee's signature and bounds give):
/// - between regions, along that relation;
/// - a part `X[L]` holds the loans of the lifetime `L` that names it: loans
///   flow into and out of it as for `L`;
/// - two alias types that are equal up to regions are the same type where
///   their regions are equal (see [`alias_region_pairs`]): the value of the
///   one flows into the other;
/// - `'static` flows into every lifetime.
///
/// What flows between `RegionsIn(T)` and a region depends on what is known
/// about `T`. Within a body, `RegionsIn(T)` flows into a region that every
/// universal region (and, for an alias, every region of it) outlives, and a
/// region into `RegionsIn(T)` only if it is `'static`. In a spec,
/// `RegionsIn(T)` flows into the regions that the solver's `T: 'r` facts
/// give.
///
/// See the [_generalized lifetime_ definition](https://prusti.github.io/pcg-docs/function-shapes.html#lifetime-projections).
///
/// [`outlives_generalized`]: crate::borrow_checker::BorrowCheckerInterface::outlives_generalized
#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From)]
pub enum GeneralizedLifetime<'tcx> {
    Region(PcgRegion<'tcx>),
    RegionsIn(OpaqueTy<'tcx>),
    /// `T[L]`: the part of the value of `T` that the bounds on `T` mentioning
    /// `L` let loans of `L` flow into or out of. For `T: Sink<'c>`, the impl
    /// of `put(&mut self, x: &'c String)` may store `x` into it, and nowhere
    /// else in the value of `T`. For an alias type, also the part made of the
    /// lifetime `L` of one of its arguments (see
    /// [`LifetimeEnv::member_lifetimes`]). It is a part of `RegionsIn(T)`,
    /// which is for moving a value of `T` as a whole.
    #[from(ignore)]
    BoundPart(OpaqueTy<'tcx>, BoundLifetime<'tcx>),
}

impl<'tcx, Ctxt: HasTyCtxt<'tcx> + DisplayCtxtFor<ty::RegionVid>> DisplayWithCtxt<Ctxt>
    for GeneralizedLifetime<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        match self {
            GeneralizedLifetime::Region(region) => region.display_output(ctxt, mode),
            GeneralizedLifetime::RegionsIn(opaque_ty) => format!("RegionsIn({opaque_ty})").into(),
            GeneralizedLifetime::BoundPart(opaque_ty, lifetime) => {
                format!("{opaque_ty}[{lifetime}]").into()
            }
        }
    }
}

/// The function whose generic parameters and where clauses the types of a
/// computation are written in. The bounds of its parameters determine the
/// [`GeneralizedLifetime::BoundPart`]s of their types.
///
/// The types of a signature name the function's lifetime parameters, those
/// of its borrow-checked body region variables. A lifetime that a where
/// clause names is named the same way as the types: in a body, a lifetime
/// parameter by its universal region variable (see [`BodyRegions`]).
#[derive(Clone, Copy)]
pub struct LifetimeEnv<'tcx> {
    pub(crate) tcx: ty::TyCtxt<'tcx>,
    pub(crate) def_id: DefId,
    /// Whether the types are those of the borrow-checked body of `def_id`.
    in_body: bool,
}

impl std::fmt::Debug for LifetimeEnv<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let kind = if self.in_body { "body" } else { "signature" };
        write!(f, "LifetimeEnv({kind} of {:?})", self.def_id)
    }
}

impl<'tcx> LifetimeEnv<'tcx> {
    /// The environment of the signature of `def_id` and of the types of its
    /// callees' signatures.
    #[must_use]
    pub fn signature(tcx: ty::TyCtxt<'tcx>, def_id: DefId) -> Self {
        Self {
            tcx,
            def_id,
            in_body: false,
        }
    }

    /// The environment of the borrow-checked body of `def_id`.
    #[must_use]
    pub fn body(tcx: ty::TyCtxt<'tcx>, def_id: DefId) -> Self {
        Self {
            tcx,
            def_id,
            in_body: true,
        }
    }

    /// This environment for the types of signatures.
    #[must_use]
    pub(crate) fn for_signature(self) -> Self {
        Self::signature(self.tcx, self.def_id)
    }

    /// `lifetime`, a lifetime of this environment, as a lifetime of
    /// [`Self::for_signature`].
    pub(crate) fn to_signature(self, lifetime: BoundLifetime<'tcx>) -> BoundLifetime<'tcx> {
        if !self.in_body {
            return lifetime;
        }
        let regions = BodyRegions::new(self.tcx, self.def_id);
        match lifetime {
            BoundLifetime::Region(region) => {
                BoundLifetime::Region(regions.vids_to_params(region.rust_region(self.tcx)).into())
            }
            BoundLifetime::RegionsIn(opaque) => BoundLifetime::RegionsIn(
                OpaqueTy::try_from(regions.vids_to_params(opaque.ty(self.tcx))).unwrap(),
            ),
        }
    }

    /// The lifetimes that name the parts of the value of `opaque_ty`, without
    /// duplicates: those that the bounds on `opaque_ty` mention, in the order
    /// of the where clauses, then for an alias type those of its arguments
    /// (see [`Self::member_lifetimes`]). Regions bound by a bound itself
    /// (`for<'x>`) and `opaque_ty` itself are not included.
    ///
    /// A type that outlives `'static` has no parts: its value holds no
    /// loans that the PCG tracks.
    pub(crate) fn bound_lifetimes(self, opaque_ty: OpaqueTy<'tcx>) -> Vec<BoundLifetime<'tcx>> {
        if self.outlives_static(opaque_ty) {
            return Vec::new();
        }
        let mut lifetimes = self.where_clause_lifetimes(opaque_ty);
        for lifetime in self.member_lifetimes(opaque_ty) {
            if !lifetimes.contains(&lifetime) {
                lifetimes.push(lifetime);
            }
        }
        lifetimes
    }

    /// Whether the value of `opaque_ty` outlives `'static` by a where clause
    /// or, for an alias type, by the bounds that its definition declares,
    /// e.g. `type B: 'static` or a supertrait `ArrayLength: 'static` of its
    /// bound (as rustc's `declared_bounds_from_definition`).
    pub(crate) fn outlives_static(self, opaque_ty: OpaqueTy<'tcx>) -> bool {
        let tcx = self.tcx;
        let ty = opaque_ty.ty(tcx);
        let erased = erase_regions(ty, tcx);
        let static_bound = |clause: ty::Clause<'tcx>, is_self: &dyn Fn(ty::Ty<'tcx>) -> bool| {
            clause.as_type_outlives_clause().is_some_and(|outlives| {
                let outlives = outlives.skip_binder();
                outlives.1.is_static() && is_self(outlives.0)
            })
        };
        let in_where_clauses = tcx
            .param_env(self.def_id)
            .caller_bounds()
            .iter()
            .any(|clause| static_bound(clause, &|bounded| erase_regions(bounded, tcx) == erased));
        let in_definition = alias_def(ty).is_some_and(|(def_id, _)| {
            // The definition's bounds are about the alias with its own
            // generic parameters.
            tcx.item_bounds(def_id).skip_binder().iter().any(|clause| {
                static_bound(clause, &|bounded| {
                    alias_def(bounded).is_some_and(|(bounded_id, _)| bounded_id == def_id)
                })
            })
        });
        in_where_clauses || in_definition
    }

    /// The lifetimes of the arguments of an alias type, of which its value is
    /// made: its region arguments that name a part (see [`names_part`]), and
    /// for an opaque
    /// type argument `Q`, `RegionsIn(Q)` and the lifetimes of the parts of
    /// `Q`. `<I as IntoIterator>::IntoIter` with `I: IntoIterator<Item = &'a
    /// u32>` has the parts `RegionsIn(I)` and `'a`: the items it yields are in
    /// the latter only. A type parameter has none.
    pub(crate) fn member_lifetimes(self, opaque_ty: OpaqueTy<'tcx>) -> Vec<BoundLifetime<'tcx>> {
        let OpaqueTy::Alias(alias) = opaque_ty else {
            return Vec::new();
        };
        let ty::TyKind::Alias(_, alias_ty) = alias.kind() else {
            unreachable!("{alias:?} is not an alias type")
        };
        let mut collector = MemberLifetimeCollector {
            env: self,
            lifetimes: Vec::new(),
        };
        alias_ty.args.visit_with(&mut collector);
        collector.lifetimes
    }

    /// The lifetimes that the where clauses on `opaque_ty` mention, in the
    /// order of the where clauses.
    pub(crate) fn where_clause_lifetimes(
        self,
        opaque_ty: OpaqueTy<'tcx>,
    ) -> Vec<BoundLifetime<'tcx>> {
        // An alias such as `<T as Tr<'a>>::Out` is matched up to its regions:
        // the types of a body have their own region variables in it.
        let self_ty = erase_regions(opaque_ty.ty(self.tcx), self.tcx);
        let is_self = |ty: ty::Ty<'tcx>| erase_regions(ty, self.tcx) == self_ty;
        let mut collector = BoundLifetimeCollector {
            of: opaque_ty,
            lifetimes: Vec::new(),
        };
        let regions = BodyRegions::new(self.tcx, self.def_id);
        for clause in self.tcx.param_env(self.def_id).caller_bounds() {
            let clause = if self.in_body {
                regions.params_to_vids(clause)
            } else {
                clause
            };
            if let Some(trait_clause) = clause.as_trait_clause() {
                let trait_ref = trait_clause.skip_binder().trait_ref;
                if is_self(trait_ref.self_ty()) {
                    trait_ref
                        .args
                        .iter()
                        .skip(1)
                        .for_each(|arg| arg.visit_with(&mut collector));
                }
            } else if let Some(projection_clause) = clause.as_projection_clause() {
                let projection = projection_clause.skip_binder();
                if is_self(projection.projection_term.self_ty()) {
                    let args = projection.projection_term.args.iter().skip(1);
                    args.for_each(|arg| arg.visit_with(&mut collector));
                    projection.term.visit_with(&mut collector);
                }
            }
        }
        collector.lifetimes
    }
}

/// Collects the lifetimes of the arguments of an alias type, for
/// [`LifetimeEnv::member_lifetimes`].
struct MemberLifetimeCollector<'tcx> {
    env: LifetimeEnv<'tcx>,
    lifetimes: Vec<BoundLifetime<'tcx>>,
}

impl<'tcx> MemberLifetimeCollector<'tcx> {
    fn push(&mut self, lifetime: BoundLifetime<'tcx>) {
        if !self.lifetimes.contains(&lifetime) {
            self.lifetimes.push(lifetime);
        }
    }
}

impl<'tcx> TypeVisitor<ty::TyCtxt<'tcx>> for MemberLifetimeCollector<'tcx> {
    fn visit_ty(&mut self, ty: ty::Ty<'tcx>) {
        match OpaqueTy::try_from(ty) {
            Ok(opaque_ty) => {
                self.push(BoundLifetime::RegionsIn(opaque_ty));
                for lifetime in self.env.bound_lifetimes(opaque_ty) {
                    self.push(lifetime);
                }
            }
            Err(()) => ty.super_visit_with(self),
        }
    }

    fn visit_region(&mut self, region: ty::Region<'tcx>) {
        if names_part(region) {
            self.push(BoundLifetime::Region(region.into()));
        }
    }
}

/// Collects the lifetimes that the arguments of a bound mention, for
/// [`LifetimeEnv::where_clause_lifetimes`].
struct BoundLifetimeCollector<'tcx> {
    of: OpaqueTy<'tcx>,
    lifetimes: Vec<BoundLifetime<'tcx>>,
}

impl<'tcx> BoundLifetimeCollector<'tcx> {
    fn push(&mut self, lifetime: BoundLifetime<'tcx>) {
        if lifetime != BoundLifetime::RegionsIn(self.of) && !self.lifetimes.contains(&lifetime) {
            self.lifetimes.push(lifetime);
        }
    }
}

impl<'tcx> TypeVisitor<ty::TyCtxt<'tcx>> for BoundLifetimeCollector<'tcx> {
    fn visit_ty(&mut self, ty: ty::Ty<'tcx>) {
        match OpaqueTy::try_from(ty) {
            Ok(opaque_ty) => self.push(BoundLifetime::RegionsIn(opaque_ty)),
            Err(()) => ty.super_visit_with(self),
        }
    }

    fn visit_region(&mut self, region: ty::Region<'tcx>) {
        // `'static` names no data that the PCG tracks, as for the arguments
        // of an alias type (see `names_part`).
        if !is_bound_region(region) && !region.is_static() {
            self.push(BoundLifetime::Region(region.into()));
        }
    }
}

struct GeneralizedLifetimeExtractor<'tcx> {
    lifetimes: Vec<GeneralizedLifetime<'tcx>>,
    env: LifetimeEnv<'tcx>,
    /// The visitor stops visiting once it has found at least this many
    /// lifetimes. The lifetimes found are then the first ones of the full
    /// list.
    limit: usize,
}

impl<'tcx> GeneralizedLifetimeExtractor<'tcx> {
    fn is_full(&self) -> bool {
        self.lifetimes.len() >= self.limit
    }

    fn push_if_absent(&mut self, gl: GeneralizedLifetime<'tcx>) {
        if !self.lifetimes.contains(&gl) {
            self.lifetimes.push(gl);
        }
    }

    /// The lifetimes of a type parameter or alias: `RegionsIn` of it, then
    /// the parts that its bounds name.
    fn push_opaque(&mut self, opaque_ty: OpaqueTy<'tcx>) {
        self.push_if_absent(GeneralizedLifetime::RegionsIn(opaque_ty));
        for lifetime in self.env.bound_lifetimes(opaque_ty) {
            self.push_if_absent(GeneralizedLifetime::BoundPart(opaque_ty, lifetime));
        }
    }
}

impl<'tcx> TypeVisitor<ty::TyCtxt<'tcx>> for GeneralizedLifetimeExtractor<'tcx> {
    fn visit_ty(&mut self, ty: ty::Ty<'tcx>) {
        if self.is_full() {
            return;
        }
        match ty.kind() {
            ty::TyKind::Param(param_ty) => self.push_opaque(OpaqueTy::Param(*param_ty)),
            ty::TyKind::Alias(..) => self.push_opaque(OpaqueTy::Alias(ty)),
            ty::TyKind::Dynamic(predicates, region, ..) => {
                self.visit_region(*region);
                predicates.visit_with(self);
            }
            // As in `LifetimeExtractor`: code, not data.
            ty::TyKind::FnPtr(_, _) | ty::TyKind::FnDef(..) => {}
            ty::TyKind::Closure(_, args) => {
                let closure_args = args.as_closure();
                for ty in closure_args.upvar_tys() {
                    self.visit_ty(ty);
                }
            }
            _ => {
                ty.super_visit_with(self);
            }
        }
    }
    fn visit_region(&mut self, rr: ty::Region<'tcx>) {
        if !self.is_full() && !is_bound_region(rr) {
            self.push_if_absent(GeneralizedLifetime::Region(rr.into()));
        }
    }
}

/// Returns the generalized lifetime list for `ty` in `env`: all regions,
/// `RegionsIn(τ)` for opaque types (type parameters, non-normalizable
/// aliases), each followed by the parts of it that its bounds name, in the
/// order they appear, with duplicates removed.
///
/// See the [`glfts(τ)` definition](https://prusti.github.io/pcg-docs/function-shapes.html#lifetime-projections).
pub(crate) fn extract_generalized_lifetimes<'tcx>(
    ty: ty::Ty<'tcx>,
    env: LifetimeEnv<'tcx>,
) -> IndexVec<LifetimeProjectionIdx<Generalized>, GeneralizedLifetime<'tcx>> {
    let mut visitor = GeneralizedLifetimeExtractor {
        lifetimes: vec![],
        env,
        limit: usize::MAX,
    };
    ty.visit_with(&mut visitor);
    visitor.lifetimes.into_iter().collect()
}

/// Whether `ty` has more than `idx` generalized lifetimes, i.e. whether `idx`
/// indexes [`extract_generalized_lifetimes`]`(ty, env)`.
pub(crate) fn has_generalized_lifetime_at<'tcx>(
    ty: ty::Ty<'tcx>,
    idx: usize,
    env: LifetimeEnv<'tcx>,
) -> bool {
    let mut visitor = GeneralizedLifetimeExtractor {
        lifetimes: vec![],
        env,
        limit: idx.saturating_add(1),
    };
    ty.visit_with(&mut visitor);
    visitor.lifetimes.len() > idx
}
