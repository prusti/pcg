use std::{borrow::Cow, collections::HashMap, marker::PhantomData};

use derive_more::{Deref, DerefMut};

use crate::{
    borrow_pcg::{
        ArgIdxOrResult, FunctionData,
        abstraction::{ArgIdx, FunctionShapeDataSource, MakeFunctionShapeError, ProjectionData},
        borrow_pcg_edge::{BlockedNode, LocalNode},
        domain::{FunctionCallAbstractionInput, FunctionCallAbstractionOutput},
        edge::abstraction::AbstractionBlockEdge,
        edge_data::{
            EdgeData, LabelEdgeLifetimeProjections, LabelEdgePlaces, LabelNodePredicate,
            NodeReplacement,
        },
        has_pcs_elem::{LabelLifetimeProjectionResult, PlaceLabeller},
        region_projection::{LifetimeProjectionLabel, PcgRegion, region_is_invariant_in_type},
        visitor::{GeneralizedLifetime, OpaqueTy, extract_generalized_lifetimes_with_bounds},
    },
    coupling::CoupledEdgeKind,
    pcg::PcgNodeWithPlace,
    rustc_interface::{
        hir::def_id::DefId,
        infer::{infer::TyCtxtInferExt, traits::ObligationCause},
        middle::{
            mir::{self, Location},
            ty::{self, GenericArgsRef},
        },
        span::{DUMMY_SP, Span, def_id::LocalDefId},
        trait_selection::{
            infer::{RegionVariableOrigin, outlives::env::OutlivesEnvironment},
            traits::{NormalizeExt, ScrubbedTraitError, TraitEngine, TraitEngineExt},
        },
    },
    utils::{
        DebugCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, HasTyCtxt, PcgPlace, Place,
        data_structures::HashSet,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        validity::{HasValidityCheck, has_validity_check_node_wrapper},
    },
};

use crate::coupling::HyperEdge;

#[derive(Clone)]
pub struct DefinedFnSigShapeDataSource<'tcx> {
    def_id: DefId,
    outlives: OutlivesEnvironment<'tcx>,
}

impl<'tcx> DefinedFnSigShapeDataSource<'tcx> {
    fn sig(&self, tcx: ty::TyCtxt<'tcx>) -> ty::FnSig<'tcx> {
        let fn_sig = tcx.fn_sig(self.def_id).instantiate_identity();
        tcx.liberate_late_bound_regions(self.def_id, fn_sig)
    }
}

impl<'tcx, Ctxt: HasTyCtxt<'tcx> + Copy> FunctionShapeDataSource<'tcx, Ctxt>
    for DefinedFnSigShapeDataSource<'tcx>
where
    PcgRegion<'tcx>: DisplayWithCtxt<Ctxt>,
{
    type Lifetime = GeneralizedLifetime<'tcx>;

    fn input_tys(&self, ctxt: Ctxt) -> Vec<ty::Ty<'tcx>> {
        self.sig(ctxt.tcx()).inputs().to_vec()
    }

    fn output_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx> {
        self.sig(ctxt.tcx()).output()
    }

    fn outlives(
        &self,
        sup: GeneralizedLifetime<'tcx>,
        sub: GeneralizedLifetime<'tcx>,
        ctxt: Ctxt,
    ) -> bool {
        if sup == sub {
            return true;
        }
        let sig = self.sig(ctxt.tcx());
        generalized_outlives(sup, sub, &self.outlives, sig.inputs(), ctxt.tcx())
    }

    fn is_invariant(
        &self,
        lifetime: GeneralizedLifetime<'tcx>,
        ty: ty::Ty<'tcx>,
        ctxt: Ctxt,
    ) -> bool {
        match lifetime {
            GeneralizedLifetime::RegionsIn(_) => true,
            GeneralizedLifetime::Region(r) => region_is_invariant_in_type(ctxt.tcx(), r, ty),
        }
    }

    fn input_arg_projections(
        &self,
        ctxt: Ctxt,
    ) -> Vec<ProjectionData<'tcx, ArgIdx, GeneralizedLifetime<'tcx>>> {
        let tbr = TraitBoundRegions::new(self.outlives.param_env);
        self.input_tys(ctxt)
            .into_iter()
            .enumerate()
            .flat_map(|(i, ty)| {
                let lifetimes = extract_generalized_lifetimes_with_bounds(ty, tbr.as_map());
                ProjectionData::nodes_for_extracted(i.into(), ty, lifetimes)
            })
            .collect()
    }

    fn result_projections(
        &self,
        ctxt: Ctxt,
    ) -> Vec<ProjectionData<'tcx, ArgIdxOrResult, GeneralizedLifetime<'tcx>>> {
        let tbr = TraitBoundRegions::new(self.outlives.param_env);
        let mut lifetimes =
            extract_generalized_lifetimes_with_bounds(self.output_ty(ctxt), tbr.as_map());

        // For type parameters in the result, we cannot know which lifetimes
        // they will capture at the call site. Add all signature lifetimes as
        // projections so that edges from any input lifetime can reach the
        // result through the type parameter.
        if matches!(self.output_ty(ctxt).kind(), ty::TyKind::Param(_)) {
            let sig = self.sig(ctxt.tcx());
            let tbr_map = tbr.as_map();
            for input_ty in sig.inputs() {
                for gl in extract_generalized_lifetimes_with_bounds(*input_ty, tbr_map) {
                    if matches!(gl, GeneralizedLifetime::Region(_))
                        && !lifetimes.iter().any(|l| *l == gl)
                    {
                        lifetimes.push(gl);
                    }
                }
            }
        }

        ProjectionData::nodes_for_extracted(ArgIdxOrResult::Result, self.output_ty(ctxt), lifetimes)
    }
}

impl<'tcx> DefinedFnSigShapeDataSource<'tcx> {
    #[rustversion::before(2025-05-24)]
    pub(crate) fn new(
        _def_id: DefId,
        _tcx: ty::TyCtxt<'tcx>,
    ) -> Result<Self, MakeFunctionShapeError> {
        Err(MakeFunctionShapeError::UnsupportedRustVersion)
    }

    #[rustversion::since(2025-05-24)]
    #[allow(clippy::unnecessary_wraps)]
    pub(crate) fn new(
        def_id: DefId,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Result<Self, MakeFunctionShapeError> {
        let typing_env = ty::TypingEnv::post_analysis(tcx, def_id);
        let (_, param_env) = tcx.infer_ctxt().build_with_typing_env(typing_env);
        let outlives = OutlivesEnvironment::from_normalized_bounds(
            param_env,
            vec![],
            vec![],
            HashSet::default(),
        );
        Ok(Self { def_id, outlives })
    }
}

/// Checks whether `sup` outlives `sub` among generalized lifetimes by
/// computing reachability in the outlives graph derived from:
///
/// 1. **Region ⇒ Region**: the free-region map (explicit `'a: 'b` bounds).
/// 2. **RegionsIn(T) ⇒ Region(r)**: `T: 'r` type-outlives bounds from
///    the param env, implied bounds from reference types in the signature,
///    or regions appearing directly in `T` itself (after substitution).
/// 3. **RegionsIn(T) ⇒ RegionsIn(T)**: reflexivity — `RegionsIn(T)`
///    represents *all* regions in `T`, so it trivially outlives itself.
///
/// Trait bounds like `T: Foo<'r>` produce **neither** `RegionsIn(T) ⇒
/// Region(r)` nor `Region(r) ⇒ RegionsIn(T)` edges. The bound constrains
/// the implementation but does not imply `T: 'r`, nor that `'r` is a
/// region "in" `T`.
fn generalized_outlives<'tcx>(
    sup: GeneralizedLifetime<'tcx>,
    sub: GeneralizedLifetime<'tcx>,
    outlives_env: &OutlivesEnvironment<'tcx>,
    input_tys: &[ty::Ty<'tcx>],
    tcx: ty::TyCtxt<'tcx>,
) -> bool {
    use crate::borrow_pcg::visitor::extract_regions;

    let param_env = outlives_env.param_env;
    let implied_type_outlives = collect_implied_type_outlives(input_tys);

    // BFS over the outlives graph starting from `sup`.
    let mut visited: HashSet<GeneralizedLifetime<'tcx>> = HashSet::default();
    let mut queue: Vec<GeneralizedLifetime<'tcx>> = vec![sup];

    while let Some(current) = queue.pop() {
        if current == sub {
            return true;
        }
        if !visited.insert(current) {
            continue;
        }
        match current {
            GeneralizedLifetime::Region(_) => {
                // No outgoing edges from Region nodes in the BFS.
                // Region → Region edges are handled after the BFS via
                // the free-region map.
            }
            GeneralizedLifetime::RegionsIn(opaque_ty) => {
                // RegionsIn(T) -> Region(r): T: 'r type-outlives bounds
                // (explicit from param env)
                let ty = opaque_ty.ty(tcx);
                for clause in param_env.caller_bounds() {
                    if let Some(bound) = clause.as_type_outlives_clause()
                        && let Some(outlives) = bound.no_bound_vars()
                        && outlives.0 == ty
                    {
                        let gl = GeneralizedLifetime::Region(outlives.1.into());
                        if !visited.contains(&gl) {
                            queue.push(gl);
                        }
                    }
                }
                // RegionsIn(T) -> Region(r): implied bounds from reference
                // types (e.g. &'b mut T implies T: 'b)
                if let Some(regions) = implied_type_outlives.get(&opaque_ty) {
                    for &r in regions {
                        let gl = GeneralizedLifetime::Region(r);
                        if !visited.contains(&gl) {
                            queue.push(gl);
                        }
                    }
                }
                // RegionsIn(T) -> Region(r): regions appearing in T itself
                // (e.g. if T is `A<'a>` which was substituted for Self)
                for r in extract_regions(ty) {
                    let gl = GeneralizedLifetime::Region(r);
                    if !visited.contains(&gl) {
                        queue.push(gl);
                    }
                }
            }
        }
    }

    // Handle Region -> Region: check the free_region_map for all visited
    // regions against the sub target.
    if let GeneralizedLifetime::Region(sub_r) = sub {
        let sub_rust = sub_r.rust_region(tcx);
        for &v in &visited {
            if let GeneralizedLifetime::Region(r) = v
                && (r.is_static()
                    || (sub_rust.is_free()
                        && r.rust_region(tcx).is_free()
                        && outlives_env.free_region_map().sub_free_regions(
                            tcx,
                            sub_rust,
                            r.rust_region(tcx),
                        )))
            {
                return true;
            }
        }
    }

    false
}

/// Per-type-parameter collection of regions that appear in trait bounds.
///
/// For bounds like `T: Foo<'a, 'b>` and `T: Bar<'c>`, stores
/// `T -> {'a, 'b, 'c}`. These are used to create additional lifetime
/// projections in the function signature (see
/// [`extract_generalized_lifetimes_with_bounds`]) and to determine
/// trait-bound region invariance, but do **not** produce edges in the
/// generalized outlives graph. The bound `T: Foo<'a>` does not imply
/// `T: 'a`, nor that `'a` is a region "in" `T`.
pub(crate) struct TraitBoundRegions<'tcx> {
    map: HashMap<OpaqueTy<'tcx>, Vec<ty::Region<'tcx>>>,
}

impl<'tcx> TraitBoundRegions<'tcx> {
    pub(crate) fn new(param_env: ty::ParamEnv<'tcx>) -> Self {
        use crate::rustc_interface::middle::ty::{TypeSuperVisitable, TypeVisitable};

        let mut map: HashMap<OpaqueTy<'tcx>, Vec<ty::Region<'tcx>>> = HashMap::default();

        for clause in param_env.caller_bounds() {
            if let Some(trait_pred) = clause.as_trait_clause() {
                let trait_pred = trait_pred.skip_binder();
                let self_ty = trait_pred.trait_ref.self_ty();
                let Ok(opaque_ty) = OpaqueTy::try_from(self_ty) else {
                    continue;
                };
                struct RegionCollector<'tcx>(Vec<ty::Region<'tcx>>);
                impl<'tcx> ty::TypeVisitor<ty::TyCtxt<'tcx>> for RegionCollector<'tcx> {
                    fn visit_region(&mut self, r: ty::Region<'tcx>) {
                        self.0.push(r);
                    }
                    fn visit_ty(&mut self, t: ty::Ty<'tcx>) {
                        t.super_visit_with(self);
                    }
                }
                let mut collector = RegionCollector(Vec::new());
                for arg in trait_pred.trait_ref.args.iter().skip(1) {
                    arg.visit_with(&mut collector);
                }
                let entry = map.entry(opaque_ty).or_default();
                for r in collector.0 {
                    if !entry.contains(&r) {
                        entry.push(r);
                    }
                }
            }
        }

        Self { map }
    }

    pub(crate) fn as_map(&self) -> &HashMap<OpaqueTy<'tcx>, Vec<ty::Region<'tcx>>> {
        &self.map
    }
}

/// Collects implied `T: 'r` bounds from reference types in the function
/// signature. For `&'r T` or `&'r mut T` where `T` is a type parameter
/// (or non-normalizable alias), well-formedness implies `T: 'r`.
fn collect_implied_type_outlives<'tcx>(
    input_tys: &[ty::Ty<'tcx>],
) -> HashMap<OpaqueTy<'tcx>, Vec<PcgRegion<'tcx>>> {
    let mut result: HashMap<OpaqueTy<'tcx>, Vec<PcgRegion<'tcx>>> = HashMap::default();
    for &ty in input_tys {
        collect_implied_bounds_from_ty(ty, &mut result);
    }
    result
}

/// Recursively extracts implied `T: 'r` bounds from a type.
///
/// For `&'r T` or `&'r mut T`:
/// - If `T` is a type parameter or non-normalizable alias, record `T: 'r`
/// - Recurses into `T` for nested references
fn collect_implied_bounds_from_ty<'tcx>(
    ty: ty::Ty<'tcx>,
    result: &mut HashMap<OpaqueTy<'tcx>, Vec<PcgRegion<'tcx>>>,
) {
    match ty.kind() {
        ty::TyKind::Ref(region, referent, _) => {
            let r: PcgRegion<'tcx> = (*region).into();
            if let Ok(opaque) = OpaqueTy::try_from(*referent) {
                let entry = result.entry(opaque).or_default();
                if !entry.contains(&r) {
                    entry.push(r);
                }
            }
            collect_implied_bounds_from_ty(*referent, result);
        }
        ty::TyKind::Adt(_, args) => {
            for arg in *args {
                if let Some(ty) = arg.as_type() {
                    collect_implied_bounds_from_ty(ty, result);
                }
            }
        }
        ty::TyKind::Tuple(tys) => {
            for ty in *tys {
                collect_implied_bounds_from_ty(ty, result);
            }
        }
        _ => {}
    }
}

pub(crate) struct FnCallDataSource<'a, 'tcx> {
    input_tys: Vec<ty::Ty<'tcx>>,
    output_ty: ty::Ty<'tcx>,
    location: Location,
    _marker: PhantomData<&'a ()>,
}

impl<'a, 'tcx: 'a> FnCallDataSource<'a, 'tcx> {
    pub(crate) fn new(
        location: Location,
        input_tys: Vec<ty::Ty<'tcx>>,
        output_ty: ty::Ty<'tcx>,
    ) -> Self {
        Self {
            location,
            input_tys,
            output_ty,
            _marker: PhantomData,
        }
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> FunctionShapeDataSource<'tcx, Ctxt>
    for FnCallDataSource<'a, 'tcx>
{
    type Lifetime = PcgRegion<'tcx>;

    fn input_tys(&self, _ctxt: Ctxt) -> Vec<ty::Ty<'tcx>> {
        self.input_tys.clone()
    }
    fn output_ty(&self, _ctxt: Ctxt) -> ty::Ty<'tcx> {
        self.output_ty
    }
    fn outlives(&self, sup: PcgRegion<'tcx>, sub: PcgRegion<'tcx>, ctxt: Ctxt) -> bool {
        ctxt.bc().outlives(sup, sub, self.location)
    }
}

pub(crate) struct DefinedFnCallShapeDataSource<'a, 'tcx> {
    call: DefinedFnCallWithCallTys<'tcx>,
    /// Maps call-site regions to their corresponding normalized sig regions.
    /// Built by walking call-site types and normalized sig types in parallel.
    region_map: HashMap<PcgRegion<'tcx>, PcgRegion<'tcx>>,
    /// Maps normalized sig regions to generalized lifetimes in the callee's
    /// identity signature. Built by structurally walking normalized and identity
    /// types in parallel. When the identity type has a type parameter `T`, all
    /// regions from the corresponding concrete type in the normalized sig map
    /// to `RegionsIn(T)`.
    norm_to_generalized_map: HashMap<PcgRegion<'tcx>, GeneralizedLifetime<'tcx>>,
    outlives: OutlivesEnvironment<'tcx>,
    _marker: PhantomData<&'a ()>,
}

impl<'a, 'tcx: 'a> DefinedFnCallShapeDataSource<'a, 'tcx> {
    #[rustversion::before(2025-05-24)]
    pub(crate) fn new(
        _call: DefinedFnCallWithCallTys<'tcx>,
        _ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<Self, MakeFunctionShapeError> {
        Err(MakeFunctionShapeError::UnsupportedRustVersion)
    }

    fn identity_input_tys(&self, tcx: ty::TyCtxt<'tcx>) -> Vec<ty::Ty<'tcx>> {
        self.call.identity_input_tys(tcx)
    }

    /// Builds a mapping from call-site regions to normalized sig regions by
    /// comparing regions at corresponding positions (by index) in the two types.
    fn build_region_map(
        call_tys: &[ty::Ty<'tcx>],
        call_result_ty: ty::Ty<'tcx>,
        normalized_sig: &ty::FnSig<'tcx>,
    ) -> HashMap<PcgRegion<'tcx>, PcgRegion<'tcx>> {
        use crate::borrow_pcg::visitor::extract_regions;
        let mut map = HashMap::default();
        for (call_ty, sig_ty) in call_tys.iter().zip(normalized_sig.inputs().iter()) {
            let call_regions = extract_regions(*call_ty);
            let sig_regions = extract_regions(*sig_ty);
            for (call_r, sig_r) in call_regions.iter().zip(sig_regions.iter()) {
                map.insert(*call_r, *sig_r);
            }
        }
        let call_result_regions = extract_regions(call_result_ty);
        let sig_result_regions = extract_regions(normalized_sig.output());
        for (call_r, sig_r) in call_result_regions.iter().zip(sig_result_regions.iter()) {
            map.insert(*call_r, *sig_r);
        }
        map
    }

    /// Builds a mapping from normalized sig regions to generalized lifetimes
    /// in the callee's identity signature by structurally walking the
    /// normalized and identity types in parallel.
    ///
    /// When the identity type has a type parameter (e.g. `Self`), the
    /// corresponding position in the normalized type contains the concrete
    /// substitute (e.g. `A<'a>`). All regions extracted from that concrete
    /// type map to `RegionsIn(Self)`.
    fn build_norm_to_generalized_map(
        normalized_sig: &ty::FnSig<'tcx>,
        identity_sig: &ty::FnSig<'tcx>,
    ) -> HashMap<PcgRegion<'tcx>, GeneralizedLifetime<'tcx>> {
        let mut map = HashMap::default();
        for (norm_ty, id_ty) in normalized_sig
            .inputs()
            .iter()
            .zip(identity_sig.inputs().iter())
        {
            Self::align_regions_to_generalized(*norm_ty, *id_ty, &mut map);
        }
        Self::align_regions_to_generalized(
            normalized_sig.output(),
            identity_sig.output(),
            &mut map,
        );
        map
    }

    /// Recursively walks a normalized type and an identity type in parallel,
    /// mapping each region in the normalized type to the corresponding
    /// `GeneralizedLifetime` in the identity type.
    fn align_regions_to_generalized(
        norm_ty: ty::Ty<'tcx>,
        id_ty: ty::Ty<'tcx>,
        map: &mut HashMap<PcgRegion<'tcx>, GeneralizedLifetime<'tcx>>,
    ) {
        use crate::borrow_pcg::visitor::extract_regions;
        match (norm_ty.kind(), id_ty.kind()) {
            // Identity type is a type parameter or non-normalizable alias: all
            // regions from the concrete normalized type map to RegionsIn(T).
            (_, ty::TyKind::Param(param_ty)) => {
                let opaque = OpaqueTy::Param(*param_ty);
                for r in extract_regions(norm_ty) {
                    map.insert(r, GeneralizedLifetime::RegionsIn(opaque));
                }
            }
            (_, ty::TyKind::Alias(_, alias_ty)) => {
                let opaque = OpaqueTy::Alias(*alias_ty);
                for r in extract_regions(norm_ty) {
                    map.insert(r, GeneralizedLifetime::RegionsIn(opaque));
                }
            }
            (ty::TyKind::Ref(norm_r, norm_referent, _), ty::TyKind::Ref(id_r, id_referent, _)) => {
                map.insert(
                    (*norm_r).into(),
                    GeneralizedLifetime::Region((*id_r).into()),
                );
                Self::align_regions_to_generalized(*norm_referent, *id_referent, map);
            }
            (ty::TyKind::Adt(norm_def, norm_args), ty::TyKind::Adt(id_def, id_args))
                if norm_def.did() == id_def.did() =>
            {
                for (norm_arg, id_arg) in norm_args.iter().zip(id_args.iter()) {
                    if let Some(norm_r) = norm_arg.as_region() {
                        if let Some(id_r) = id_arg.as_region() {
                            map.insert(norm_r.into(), GeneralizedLifetime::Region(id_r.into()));
                        }
                    } else if let Some(norm_inner) = norm_arg.as_type()
                        && let Some(id_inner) = id_arg.as_type()
                    {
                        Self::align_regions_to_generalized(norm_inner, id_inner, map);
                    }
                }
            }
            (ty::TyKind::Tuple(norm_tys), ty::TyKind::Tuple(id_tys)) => {
                for (norm_inner, id_inner) in norm_tys.iter().zip(id_tys.iter()) {
                    Self::align_regions_to_generalized(norm_inner, id_inner, map);
                }
            }
            (ty::TyKind::Slice(norm_inner), ty::TyKind::Slice(id_inner))
            | (ty::TyKind::Array(norm_inner, _), ty::TyKind::Array(id_inner, _))
            | (ty::TyKind::RawPtr(norm_inner, _), ty::TyKind::RawPtr(id_inner, _)) => {
                Self::align_regions_to_generalized(*norm_inner, *id_inner, map);
            }
            // Dynamic types: map the region.
            (ty::TyKind::Dynamic(_, norm_r, ..), ty::TyKind::Dynamic(_, id_r, ..)) => {
                map.insert(
                    (*norm_r).into(),
                    GeneralizedLifetime::Region((*id_r).into()),
                );
            }
            _ => {}
        }
    }

    #[rustversion::since(2025-05-24)]
    #[allow(clippy::unnecessary_wraps)]
    pub(crate) fn new(
        call: DefinedFnCallWithCallTys<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<Self, MakeFunctionShapeError> {
        // Use the callee's typing env for outlives checks, since after mapping
        // regions back to identity regions, we need the callee's param env
        // constraints (e.g. `'b: 'a`).
        let callee_typing_env = ty::TypingEnv::post_analysis(ctxt.tcx(), call.fn_def_id());
        let (_, param_env) = ctxt
            .tcx()
            .infer_ctxt()
            .build_with_typing_env(callee_typing_env);
        let outlives = OutlivesEnvironment::from_normalized_bounds(
            param_env,
            vec![],
            vec![],
            HashSet::default(),
        );
        let normalized = call.defined_fn_call.normalized_sig(ctxt);
        let identity = call
            .defined_fn_call
            .function_data
            .identity_fn_sig(ctxt.tcx());
        let region_map =
            Self::build_region_map(&call.call_arg_tys, call.call_result_ty, &normalized);
        let norm_to_generalized_map = Self::build_norm_to_generalized_map(&normalized, &identity);
        Ok(Self {
            call,
            outlives,
            region_map,
            norm_to_generalized_map,
            _marker: PhantomData,
        })
    }
}

impl<'tcx> FunctionData<'tcx> {
    #[must_use]
    pub fn identity_fn_sig(self, tcx: ty::TyCtxt<'tcx>) -> ty::FnSig<'tcx> {
        let fn_sig = tcx.fn_sig(self.def_id).instantiate_identity();
        tcx.liberate_late_bound_regions(self.def_id, fn_sig)
    }

    /// Returns the function signature instantiated with the given substs (but
    /// not normalized).
    #[must_use]
    pub fn fn_sig(self, tcx: ty::TyCtxt<'tcx>, substs: GenericArgsRef<'tcx>) -> ty::FnSig<'tcx> {
        let fn_sig = tcx.fn_sig(self.def_id).instantiate(tcx, substs);
        tcx.liberate_late_bound_regions(self.def_id, fn_sig)
    }
}

impl<'a, 'tcx: 'a> DefinedFnCallShapeDataSource<'a, 'tcx> {
    /// Maps a normalized sig region to a generalized lifetime in the callee's
    /// identity signature.
    ///
    /// First checks the pre-built `norm_to_generalized_map` (which handles
    /// both late-bound regions and regions hidden inside type parameters),
    /// then falls back to searching `caller_substs` for early-bound region
    /// variables.
    fn normalized_to_identity(
        &self,
        region: PcgRegion<'tcx>,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Option<GeneralizedLifetime<'tcx>> {
        match region {
            PcgRegion::ReLateParam(_) | PcgRegion::ReStatic | PcgRegion::ReEarlyParam(_) => {
                Some(GeneralizedLifetime::Region(region))
            }
            PcgRegion::RegionVid(_) => {
                // First try the structural map, which captures late-bound
                // regions and regions inside type parameters.
                if let Some(&gl) = self.norm_to_generalized_map.get(&region) {
                    return Some(gl);
                }
                // Fall back to searching caller_substs for early-bound regions.
                let caller_substs = self.call.caller_substs();
                let index = caller_substs.iter().position(|arg| {
                    arg.as_region()
                        .is_some_and(|r| PcgRegion::from(r) == region)
                })?;
                let fn_ty = tcx.type_of(self.call.fn_def_id()).instantiate_identity();
                let ty::TyKind::FnDef(_def_id, identity_substs) = fn_ty.kind() else {
                    panic!("Expected a function type");
                };
                Some(GeneralizedLifetime::Region(
                    identity_substs.region_at(index).into(),
                ))
            }
            _ => None,
        }
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> FunctionShapeDataSource<'tcx, Ctxt>
    for DefinedFnCallShapeDataSource<'a, 'tcx>
{
    type Lifetime = PcgRegion<'tcx>;

    fn input_tys(&self, _ctxt: Ctxt) -> Vec<ty::Ty<'tcx>> {
        self.call.call_arg_tys.clone()
    }
    fn output_ty(&self, _ctxt: Ctxt) -> ty::Ty<'tcx> {
        self.call.call_result_ty
    }

    fn outlives(&self, sup: PcgRegion<'tcx>, sub: PcgRegion<'tcx>, ctxt: Ctxt) -> bool {
        if sup.is_static() || sup == sub {
            return true;
        }

        // Map call-site regions to normalized sig regions.
        let sup_norm = self.region_map.get(&sup).copied();
        let sub_norm = self.region_map.get(&sub).copied();

        // If both map to the same normalized region, they represent the same
        // lifetime in the callee's signature — outlives holds.
        if let (Some(s), Some(t)) = (sup_norm, sub_norm)
            && s == t
        {
            return true;
        }

        // Map to generalized lifetimes in the identity signature and check
        // outlives using the generalized lifetime graph (which handles trait
        // bounds, type parameters, and implied bounds).
        let Some(sup_gl) = sup_norm.and_then(|r| self.normalized_to_identity(r, ctxt.tcx())) else {
            return false;
        };
        let Some(sub_gl) = sub_norm.and_then(|r| self.normalized_to_identity(r, ctxt.tcx())) else {
            return false;
        };
        if sup_gl == sub_gl {
            return true;
        }
        let identity_input_tys = self.identity_input_tys(ctxt.tcx());
        if generalized_outlives(
            sup_gl,
            sub_gl,
            &self.outlives,
            &identity_input_tys,
            ctxt.tcx(),
        ) {
            return true;
        }

        // When the identity result type is a type parameter T and `sub`
        // maps to `RegionsIn(T)`, the concrete call-site region is "inside"
        // T at the call site. Since T could contain borrows under any
        // signature lifetime, check whether `sup_gl` outlives any of them.
        //
        // This only applies when T IS the identity result type — not when
        // RegionsIn(T) arises from an input type parameter like Self.
        let identity_result_ty = self
            .call
            .defined_fn_call
            .function_data
            .identity_fn_sig(ctxt.tcx())
            .output();
        if let GeneralizedLifetime::RegionsIn(opaque_ty) = sub_gl
            && opaque_ty.is_param()
            && opaque_ty.ty(ctxt.tcx()) == identity_result_ty
        {
            let param_ty = opaque_ty.ty(ctxt.tcx());
            let tbr = TraitBoundRegions::new(self.outlives.param_env);
            let tbr_map = tbr.as_map();
            let bound_regions = extract_generalized_lifetimes_with_bounds(param_ty, tbr_map);
            for gl in bound_regions {
                if matches!(gl, GeneralizedLifetime::Region(_))
                    && generalized_outlives(
                        sup_gl,
                        gl,
                        &self.outlives,
                        &identity_input_tys,
                        ctxt.tcx(),
                    )
                {
                    return true;
                }
            }
            // Also check against all signature lifetimes (since T could
            // contain borrows under any of them).
            for input_ty in &identity_input_tys {
                for gl in extract_generalized_lifetimes_with_bounds(*input_ty, tbr_map) {
                    if matches!(gl, GeneralizedLifetime::Region(_))
                        && generalized_outlives(
                            sup_gl,
                            gl,
                            &self.outlives,
                            &identity_input_tys,
                            ctxt.tcx(),
                        )
                    {
                        return true;
                    }
                }
            }
        }
        false
    }
}

pub(crate) type FunctionCallAbstractionEdge<'tcx, P = Place<'tcx>> = AbstractionBlockEdge<
    'tcx,
    FunctionCallAbstractionInput<'tcx, P>,
    FunctionCallAbstractionOutput<'tcx>,
>;

impl<'tcx> FunctionCallAbstractionEdge<'tcx> {
    #[must_use]
    pub fn to_hyper_edge(
        &self,
    ) -> HyperEdge<FunctionCallAbstractionInput<'tcx>, FunctionCallAbstractionOutput<'tcx>> {
        HyperEdge::new(vec![self.input], vec![self.output])
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Deref, DerefMut)]
pub struct AbstractionBlockEdgeWithMetadata<Metadata, Edge> {
    pub(crate) metadata: Metadata,
    #[deref]
    #[deref_mut]
    pub(crate) edge: Edge,
}

impl<Metadata, Input: Copy, Output: Copy>
    AbstractionBlockEdgeWithMetadata<Metadata, AbstractionBlockEdge<'_, Input, Output>>
{
    pub(crate) fn into_singleton_coupled_edge(self) -> CoupledEdgeKind<Metadata, Input, Output> {
        CoupledEdgeKind::new(self.metadata, self.edge.to_singleton_hyper_edge())
    }
}

pub struct DefinedFnCallWithCallTys<'tcx> {
    pub(crate) defined_fn_call: DefinedFnCall<'tcx>,
    pub(crate) call_arg_tys: Vec<ty::Ty<'tcx>>,
    pub(crate) call_result_ty: ty::Ty<'tcx>,
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for DefinedFnCallWithCallTys<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        DisplayOutput::join(
            vec![
                self.defined_fn_call.display_output(ctxt, mode),
                format!("call_arg_tys: {:?}", self.call_arg_tys).into(),
                format!("call_result_ty: {:?}", self.call_result_ty).into(),
            ],
            &DisplayOutput::NEWLINE,
        )
    }
}

impl<'tcx> DefinedFnCallWithCallTys<'tcx> {
    pub(crate) fn identity_input_tys(&self, tcx: ty::TyCtxt<'tcx>) -> Vec<ty::Ty<'tcx>> {
        self.defined_fn_call
            .function_data
            .identity_fn_sig(tcx)
            .inputs()
            .to_vec()
    }

    #[must_use]
    pub fn fn_def_id(&self) -> DefId {
        self.defined_fn_call.function_data.def_id
    }

    #[must_use]
    pub fn caller_substs(&self) -> GenericArgsRef<'tcx> {
        self.defined_fn_call.caller_substs
    }

    pub(crate) fn new(
        defined_fn_call: DefinedFnCall<'tcx>,
        arg_tys: Vec<ty::Ty<'tcx>>,
        result_ty: ty::Ty<'tcx>,
    ) -> Self {
        Self {
            defined_fn_call,
            call_arg_tys: arg_tys,
            call_result_ty: result_ty,
        }
    }

    pub fn from_terminator<'a>(
        terminator: &mir::Terminator<'tcx>,
        caller_def_id: LocalDefId,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Option<Self>
    where
        'tcx: 'a,
    {
        if let mir::TerminatorKind::Call {
            ref func,
            ref args,
            destination,
            fn_span,
            ..
        } = terminator.kind
            && let ty::TyKind::FnDef(def_id, substs) = func.ty(ctxt.body(), ctxt.tcx()).kind()
        {
            let defined_fn_call =
                DefinedFnCall::new(FunctionData::new(*def_id), substs, caller_def_id, fn_span);
            Some(Self {
                defined_fn_call,
                call_arg_tys: args
                    .iter()
                    .map(|arg| arg.node.ty(ctxt.body(), ctxt.tcx()))
                    .collect(),
                call_result_ty: destination.ty(ctxt.body(), ctxt.tcx()).ty,
            })
        } else {
            None
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub struct DefinedFnCall<'tcx> {
    pub(crate) function_data: FunctionData<'tcx>,
    pub(crate) caller_substs: GenericArgsRef<'tcx>,
    pub(crate) caller_def_id: LocalDefId,
    pub(crate) span: Span,
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for DefinedFnCall<'tcx>
{
    #[rustversion::before(2025-05-24)]
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        let identity_sig = self.function_data.identity_fn_sig(ctxt.tcx());
        let subst_sig = self.function_data.fn_sig(ctxt.tcx(), self.caller_substs);
        DisplayOutput::join(
            vec![
                "--------------------------------".into(),
                DisplayOutput::join(
                    vec![
                        self.function_data.display_output(ctxt, mode),
                        "at".into(),
                        format!("{:?}", self.span).into(),
                    ],
                    &DisplayOutput::SPACE,
                ),
                format!("identity_sig: {identity_sig}").into(),
                format!("caller_substs: {:?}", self.caller_substs).into(),
                format!("subst_sig: {subst_sig}").into(),
                format!("caller_def_id: {:?}", self.caller_def_id).into(),
                format!("span: {:?}", self.span).into(),
                "--------------------------------".into(),
            ],
            &"\n".into(),
        )
    }

    #[rustversion::since(2025-05-24)]
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        let identity_sig = self.function_data.identity_fn_sig(ctxt.tcx());
        let subst_sig = self.function_data.fn_sig(ctxt.tcx(), self.caller_substs);
        DisplayOutput::join(
            vec![
                "--------------------------------".into(),
                DisplayOutput::join(
                    vec![
                        self.function_data.display_output(ctxt, mode),
                        "at".into(),
                        format!("{:?}", self.span).into(),
                    ],
                    &DisplayOutput::SPACE,
                ),
                format!("identity_sig: {identity_sig}").into(),
                format!("caller_substs: {:?}", self.caller_substs).into(),
                format!("subst_sig: {subst_sig}").into(),
                format!("normalized_sig: {}", self.normalized_sig(ctxt)).into(),
                format!("callee_param_env: {:?}", self.callee_param_env(ctxt)).into(),
                format!("caller_def_id: {:?}", self.caller_def_id).into(),
                format!("span: {:?}", self.span).into(),
                "--------------------------------".into(),
            ],
            &"\n".into(),
        )
    }
}

impl<'tcx> DefinedFnCall<'tcx> {
    pub fn new(
        function_data: FunctionData<'tcx>,
        caller_substs: GenericArgsRef<'tcx>,
        caller_def_id: LocalDefId,
        span: Span,
    ) -> Self {
        Self {
            function_data,
            caller_substs,
            caller_def_id,
            span,
        }
    }

    #[rustversion::since(2025-05-24)]
    pub(crate) fn callee_param_env<'a>(
        &self,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> ty::ParamEnv<'tcx>
    where
        'tcx: 'a,
    {
        ty::TypingEnv::post_analysis(ctxt.tcx(), self.function_data.def_id)
            .with_post_analysis_normalized(ctxt.tcx())
            .param_env
    }

    #[rustversion::since(2025-05-24)]
    pub(crate) fn normalized_sig<'a>(
        &self,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> ty::FnSig<'tcx>
    where
        'tcx: 'a,
    {
        let caller_typing_env = ty::TypingEnv::post_analysis(ctxt.tcx(), self.caller_def_id)
            .with_post_analysis_normalized(ctxt.tcx());
        let (infcx, param_env) = ctxt
            .tcx()
            .infer_ctxt()
            .build_with_typing_env(caller_typing_env);
        let subst_sig = self.function_data.fn_sig(ctxt.tcx(), self.caller_substs);
        // Pre-populate the inference context with region variables so that
        // their indices align with the borrow checker's `RegionVid`s.
        // Without this, `deeply_normalize` panics when it encounters region
        // variables that don't exist in the inference context. This is a hack;
        // we should find a better way to set up normalization.
        for _ in ctxt.bc_ctxt().borrow_checker().iter_region_vids() {
            infcx.next_region_var(RegionVariableOrigin::Misc(DUMMY_SP));
        }
        let mut fulfill_cx = <dyn TraitEngine<ScrubbedTraitError> as TraitEngineExt<
            ScrubbedTraitError,
        >>::new(&infcx);
        infcx
            .at(&ObligationCause::dummy(), param_env)
            .deeply_normalize(subst_sig, &mut *fulfill_cx)
            .unwrap()
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub struct FunctionCallAbstractionEdgeMetadata<'tcx> {
    pub(crate) location: Location,
    pub(crate) defined_fn_call: Option<DefinedFnCall<'tcx>>,
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for FunctionCallAbstractionEdgeMetadata<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(
            format!(
                "call{} at {:?}",
                if let Some(defined_fn_call) = &self.defined_fn_call {
                    format!(
                        " {}",
                        ctxt.tcx()
                            .def_path_str(defined_fn_call.function_data.def_id)
                    )
                } else {
                    String::new()
                },
                self.location
            )
            .into(),
        )
    }
}
impl<'tcx> FunctionCallAbstractionEdgeMetadata<'tcx> {
    #[must_use]
    pub fn location(&self) -> Location {
        self.location
    }

    #[must_use]
    pub fn def_id(&self) -> Option<DefId> {
        self.defined_fn_call
            .as_ref()
            .map(|f| f.function_data.def_id)
    }

    #[must_use]
    pub fn function_data(&self) -> Option<FunctionData<'tcx>> {
        self.defined_fn_call.as_ref().map(|f| f.function_data)
    }
}

pub type FunctionCallAbstraction<'tcx, P = Place<'tcx>> = AbstractionBlockEdgeWithMetadata<
    FunctionCallAbstractionEdgeMetadata<'tcx>,
    FunctionCallAbstractionEdge<'tcx, P>,
>;

impl<'tcx, Ctxt: Copy, P: PcgPlace<'tcx, Ctxt>> LabelEdgeLifetimeProjections<'tcx, Ctxt, P>
    for FunctionCallAbstraction<'tcx, P>
where
    FunctionCallAbstractionEdge<'tcx, P>: LabelEdgeLifetimeProjections<'tcx, Ctxt, P>,
{
    fn label_lifetime_projections(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: Ctxt,
    ) -> LabelLifetimeProjectionResult {
        self.edge.label_lifetime_projections(predicate, label, ctxt)
    }
}

impl<'tcx, Ctxt: DebugCtxt, P: PcgPlace<'tcx, Ctxt>> LabelEdgePlaces<'tcx, Ctxt, P>
    for FunctionCallAbstraction<'tcx, P>
where
    FunctionCallAbstractionEdge<'tcx, P>: LabelEdgePlaces<'tcx, Ctxt, P>,
{
    fn label_blocked_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>> {
        self.edge.label_blocked_places(predicate, labeller, ctxt)
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>> {
        self.edge.label_blocked_by_places(predicate, labeller, ctxt)
    }
}

impl<'tcx, Ctxt: Copy + DebugCtxt, P: PcgPlace<'tcx, Ctxt>> EdgeData<'tcx, Ctxt, P>
    for FunctionCallAbstraction<'tcx, P>
where
    FunctionCallAbstractionEdge<'tcx, P>: EdgeData<'tcx, Ctxt, P>,
{
    fn blocks_node<'slf>(&self, node: BlockedNode<'tcx, P>, ctxt: Ctxt) -> bool {
        self.edge.blocks_node(node, ctxt)
    }

    fn blocked_nodes<'slf>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Box<dyn std::iter::Iterator<Item = PcgNodeWithPlace<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        self.edge.blocked_nodes(ctxt)
    }

    fn blocked_by_nodes<'slf>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        self.edge.blocked_by_nodes(ctxt)
    }
}

has_validity_check_node_wrapper!(FunctionCallAbstraction<'tcx, P>);

impl<Ctxt: Copy, Metadata: DisplayWithCtxt<Ctxt>, Edge: DisplayWithCtxt<Ctxt>> DisplayWithCtxt<Ctxt>
    for AbstractionBlockEdgeWithMetadata<Metadata, Edge>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Seq(vec![
            self.metadata.display_output(ctxt, mode),
            DisplayOutput::Text(Cow::Borrowed(": ")),
            self.edge.display_output(ctxt, mode),
        ])
    }
}

impl<'tcx> FunctionCallAbstraction<'tcx> {
    #[must_use]
    pub fn def_id(&self) -> Option<DefId> {
        self.metadata.function_data().as_ref().map(|f| f.def_id)
    }
    #[must_use]
    pub fn substs(&self) -> Option<GenericArgsRef<'tcx>> {
        self.metadata
            .defined_fn_call
            .as_ref()
            .map(|f| f.caller_substs)
    }

    #[must_use]
    pub fn location(&self) -> Location {
        self.metadata.location
    }

    #[must_use]
    pub fn edge(
        &self,
    ) -> &AbstractionBlockEdge<
        'tcx,
        FunctionCallAbstractionInput<'tcx>,
        FunctionCallAbstractionOutput<'tcx>,
    > {
        &self.edge
    }

    #[must_use]
    pub fn new(
        metadata: FunctionCallAbstractionEdgeMetadata<'tcx>,
        edge: AbstractionBlockEdge<
            'tcx,
            FunctionCallAbstractionInput<'tcx>,
            FunctionCallAbstractionOutput<'tcx>,
        >,
    ) -> Self {
        Self { metadata, edge }
    }
}
