use crate::{
    HasSettings, Sealed,
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        borrow_pcg_expansion::PlaceExpansion,
        region_projection::{OverrideRegionDebugString, PcgRegion, TyVarianceVisitor},
    },
    error::{PcgError, PcgUnsupportedError},
    owned_pcg::RepackGuide,
    pcg::ctxt::AnalysisCtxt,
    pcg_validity_assert,
    rustc_interface::{
        FieldIdx, PlaceTy, RustBitSet,
        middle::{
            mir::{
                BasicBlock, Body, HasLocalDecls, Local, Mutability, Place as MirPlace, PlaceElem,
                ProjectionElem, VarDebugInfoContents,
            },
            ty::{self, TyCtxt, TyKind, TypeVisitable},
        },
        mir_dataflow,
        span::{Span, SpanSnippetError, def_id::LocalDefId},
    },
    utils::{PlaceLike, place::Place, validity::HasValidityCheck},
    validity_checks_enabled,
};

#[derive(Copy, Clone)]
pub struct CompilerCtxt<'a, 'tcx, T = &'a dyn BorrowCheckerInterface<'tcx>> {
    pub(crate) mir: &'a Body<'tcx>,
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) borrow_checker: T,
}

impl<T> Sealed for CompilerCtxt<'_, '_, T> {}

impl<BC: OverrideRegionDebugString + ?Sized> OverrideRegionDebugString
    for CompilerCtxt<'_, '_, &BC>
{
    fn override_region_debug_string(&self, region: ty::RegionVid) -> Option<&str> {
        self.borrow_checker.override_region_debug_string(region)
    }
}

impl OverrideRegionDebugString for CompilerCtxt<'_, '_, ()> {
    fn override_region_debug_string(&self, _region: ty::RegionVid) -> Option<&str> {
        None
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> LocalTys<'tcx> for Ctxt {
    fn local_ty(&self, local: Local) -> ty::Ty<'tcx> {
        self.ctxt().body().local_decls[local].ty
    }
}

impl<'a, 'tcx, T: Copy> DebugCtxt for CompilerCtxt<'a, 'tcx, T>
where
    CompilerCtxt<'a, 'tcx, T>: OverrideRegionDebugString,
{
    fn func_name(&self) -> String {
        self.tcx
            .def_path_str(self.mir.source.def_id().expect_local())
    }
    fn num_basic_blocks(&self) -> usize {
        self.mir.basic_blocks.len()
    }
}

impl<'tcx, T: Copy> HasTyCtxt<'tcx> for CompilerCtxt<'_, 'tcx, T> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl<T: Copy> std::fmt::Debug for CompilerCtxt<'_, '_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CompilerCtxt",)
    }
}

impl<'a, 'tcx, T: BorrowCheckerInterface<'tcx> + ?Sized> CompilerCtxt<'a, 'tcx, &'a T> {
    pub fn as_dyn(self) -> CompilerCtxt<'a, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>> {
        CompilerCtxt {
            mir: self.mir,
            tcx: self.tcx(),
            borrow_checker: self.borrow_checker.as_dyn(),
        }
    }
}

impl<'a, 'tcx, T> CompilerCtxt<'a, 'tcx, T> {
    pub fn new(mir: &'a Body<'tcx>, tcx: TyCtxt<'tcx>, borrow_checker: T) -> Self {
        Self {
            mir,
            tcx,
            borrow_checker,
        }
    }

    pub fn body(self) -> &'a Body<'tcx> {
        self.mir
    }

    pub fn tcx(self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn source_of_span(&self, sp: Span) -> Result<String, SpanSnippetError> {
        let source_map = self.tcx.sess.source_map();
        source_map.span_to_snippet(sp)
    }

    pub fn source(&self) -> Result<String, SpanSnippetError> {
        self.source_of_span(self.mir.span)
    }

    pub fn source_lines(&self) -> Result<Vec<String>, SpanSnippetError> {
        let source = self.source()?;
        Ok(source.lines().map(|l| l.to_owned()).collect::<Vec<_>>())
    }

    pub fn borrow_checker(self) -> T
    where
        T: Copy,
    {
        self.borrow_checker
    }

    #[deprecated(note = "Use `.borrow_checker()` instead")]
    pub fn bc(self) -> T
    where
        T: Copy,
    {
        self.borrow_checker
    }

    pub fn body_def_path_str(&self) -> String {
        self.tcx.def_path_str(self.def_id())
    }

    pub fn local_place(&self, var_name: &str) -> Option<Place<'tcx>> {
        for info in &self.mir.var_debug_info {
            if let VarDebugInfoContents::Place(place) = info.value
                && info.name.to_string() == var_name
            {
                return Some(place.into());
            }
        }
        None
    }

    pub(crate) fn def_id(&self) -> LocalDefId {
        self.mir.source.def_id().expect_local()
    }
}

impl CompilerCtxt<'_, '_> {
    /// Returns `true` iff the edge from `from` to `to` is a back edge (i.e.
    /// `to` dominates `from`).
    pub(crate) fn is_back_edge(&self, from: BasicBlock, to: BasicBlock) -> bool {
        self.mir.basic_blocks.dominators().dominates(to, from)
    }

    pub fn num_args(self) -> usize {
        self.mir.arg_count
    }

    pub fn local_count(self) -> usize {
        self.mir.local_decls().len()
    }

    pub fn always_live_locals(self) -> RustBitSet<Local> {
        mir_dataflow::impls::always_storage_live_locals(self.mir)
    }

    pub fn always_live_locals_non_args(self) -> RustBitSet<Local> {
        let mut all = self.always_live_locals();
        for arg in 0..self.mir.arg_count + 1 {
            // Includes `RETURN_PLACE`
            all.remove(arg.into());
        }
        all
    }
}

impl<'a, 'tcx, T: Copy> HasCompilerCtxt<'a, 'tcx> for CompilerCtxt<'a, 'tcx, T> {
    fn ctxt(self) -> CompilerCtxt<'a, 'tcx, ()> {
        CompilerCtxt::new(self.mir, self.tcx, ())
    }

    fn body(self) -> &'a Body<'tcx> {
        self.mir
    }
}

impl<'a, 'tcx, T: Copy> HasBorrowCheckerCtxt<'a, 'tcx, T> for CompilerCtxt<'a, 'tcx, T>
where
    CompilerCtxt<'a, 'tcx, T>: OverrideRegionDebugString,
{
    fn bc(&self) -> T {
        self.borrow_checker
    }

    fn bc_ctxt(&self) -> CompilerCtxt<'a, 'tcx, T> {
        *self
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ProjectionKind {
    DerefRef(Mutability),
    DerefRawPtr(Mutability),
    DerefBox,
    Field(FieldIdx),
    ConstantIndex(ConstantIndex),
    Other,
}
// TODO: Merge with ExpandedPlace?
#[derive(Clone)]
pub struct ShallowExpansion<'tcx> {
    pub(crate) target_place: Place<'tcx>,

    /// Other places that could have resulted from this expansion. Note: this
    /// vector is always incomplete when projecting with `Index` or `Subslice`
    /// and also when projecting a slice type with `ConstantIndex`!
    pub(crate) other_places: Vec<Place<'tcx>>,
    pub(crate) kind: ProjectionKind,
}

impl<'tcx> ShallowExpansion<'tcx> {
    pub(crate) fn new<'a>(
        target_place: Place<'tcx>,
        other_places: Vec<Place<'tcx>>,
        kind: ProjectionKind,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Self
    where
        'tcx: 'a,
    {
        if validity_checks_enabled() && matches!(kind, ProjectionKind::DerefRef(_)) {
            pcg_validity_assert!(!target_place.is_owned(ctxt));
        }
        Self {
            target_place,
            other_places,
            kind,
        }
    }

    pub(crate) fn base_place(&self) -> Place<'tcx> {
        self.target_place.last_projection().unwrap().0
    }

    pub(crate) fn guide(&self) -> Option<RepackGuide> {
        self.target_place
            .last_projection()
            .unwrap()
            .1
            .try_into()
            .ok()
    }

    pub fn expansion(&self) -> Vec<Place<'tcx>> {
        let mut expansion = self.other_places.clone();
        self.kind
            .insert_target_into_expansion(self.target_place, &mut expansion);
        expansion
    }

    fn dest_places_for_region<'a>(
        &self,
        region: PcgRegion,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Vec<Place<'tcx>>
    where
        'tcx: 'a,
    {
        self.expansion()
            .iter()
            .filter(|e| {
                e.lifetime_projections(ctxt)
                    .into_iter()
                    .any(|child_rp| region == child_rp.region(ctxt.ctxt()))
            })
            .copied()
            .collect::<Vec<_>>()
    }

    pub(crate) fn place_expansion_for_region<'a>(
        &self,
        region: PcgRegion,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Option<PlaceExpansion<'tcx>>
    where
        'tcx: 'a,
    {
        let dest_places = self.dest_places_for_region(region, ctxt);
        if dest_places.is_empty() {
            None
        } else {
            Some(PlaceExpansion::from_places(dest_places, ctxt))
        }
    }
}

impl ProjectionKind {
    pub(crate) fn is_deref_box(self) -> bool {
        matches!(self, ProjectionKind::DerefBox)
    }

    pub(crate) fn insert_target_into_expansion<'tcx>(
        self,
        target: Place<'tcx>,
        expansion: &mut Vec<Place<'tcx>>,
    ) {
        match self {
            ProjectionKind::Field(field_idx) => {
                expansion.insert(field_idx.index(), target);
            }
            _ => {
                expansion.push(target);
            }
        }
    }
}

pub trait DebugCtxt: OverrideRegionDebugString {
    fn func_name(&self) -> String;
    fn num_basic_blocks(&self) -> usize;
}

pub trait LocalTys<'tcx> {
    fn local_ty(&self, local: Local) -> ty::Ty<'tcx>;
}

pub(crate) trait HasLocals: Copy {
    fn always_live_locals(self) -> RustBitSet<Local>;
    fn arg_count(self) -> usize;
    fn local_count(self) -> usize;
    fn args_iter(self) -> Box<dyn Iterator<Item = Local> + 'static> {
        // For a function with `N` arguments, the local _0 is the return place,
        // and the arguments are _1, ..., _N.
        Box::new((1..self.arg_count() + 1).map(Local::from_usize))
    }
}

pub trait HasCompilerCtxt<'a, 'tcx>: HasTyCtxt<'tcx> + Copy {
    fn ctxt(self) -> CompilerCtxt<'a, 'tcx, ()>;
    fn body(self) -> &'a Body<'tcx> {
        self.ctxt().body()
    }
}

pub(crate) trait DataflowCtxt<'a, 'tcx: 'a>:
    HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>
{
    fn try_into_analysis_ctxt(self) -> Option<AnalysisCtxt<'a, 'tcx>>;
}
pub trait HasBorrowCheckerCtxt<'a, 'tcx, BC = &'a dyn BorrowCheckerInterface<'tcx>>:
    HasCompilerCtxt<'a, 'tcx> + DebugCtxt
{
    fn bc(&self) -> BC;
    fn bc_ctxt(&self) -> CompilerCtxt<'a, 'tcx, BC>;
}

pub trait HasTyCtxt<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx>;

    fn region_is_invariant_in_type(&self, region: PcgRegion, ty: ty::Ty<'tcx>) -> bool {
        let mut visitor = TyVarianceVisitor {
            tcx: self.tcx(),
            target: region,
            found: false,
        };
        ty.visit_with(&mut visitor);
        visitor.found
    }
}

impl<'tcx> HasTyCtxt<'tcx> for TyCtxt<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        *self
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct ConstantIndex {
    pub(crate) offset: u64,
    pub(crate) min_length: u64,
    pub(crate) from_end: bool,
}

impl From<ConstantIndex> for PlaceElem<'_> {
    fn from(val: ConstantIndex) -> Self {
        PlaceElem::ConstantIndex {
            offset: val.offset,
            min_length: val.min_length,
            from_end: val.from_end,
        }
    }
}

impl ConstantIndex {
    pub(crate) fn other_places<'a, 'tcx>(
        self,
        from: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Vec<Place<'tcx>>
    where
        'tcx: 'a,
    {
        self.other_elems()
            .into_iter()
            .map(|e| from.project_deeper(e, ctxt).unwrap())
            .collect()
    }

    pub(crate) fn other_elems<'tcx>(self) -> Vec<PlaceElem<'tcx>> {
        let range = if self.from_end {
            1..self.min_length + 1
        } else {
            0..self.min_length
        };
        assert!(range.contains(&self.offset));
        range
            .filter(|&i| i != self.offset)
            .map(|i| ProjectionElem::ConstantIndex {
                offset: i,
                min_length: self.min_length,
                from_end: self.from_end,
            })
            .collect()
    }
}

impl<'tcx> Place<'tcx> {
    pub fn to_rust_place<'a>(self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> MirPlace<'tcx>
    where
        'tcx: 'a,
    {
        MirPlace {
            local: self.local,
            projection: ctxt.tcx().mk_place_elems(self.projection),
        }
    }

    /// Expand `self` one level down by following the `guide_place`.
    /// Returns the new `self` and a vector containing other places that
    /// could have resulted from the expansion.
    pub fn expand_one_level<'a>(
        self,
        guide_place: Self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Result<ShallowExpansion<'tcx>, PcgError>
    where
        'tcx: 'a,
    {
        let index = self.projection.len();
        assert!(
            index < guide_place.projection.len(),
            "self place {self:?} is not a prefix of guide place {guide_place:?}"
        );
        let new_projection = ctxt.tcx().mk_place_elems_from_iter(
            self.projection
                .iter()
                .copied()
                .chain([guide_place.projection[index]]),
        );
        let new_current_place = Place::new(self.local, new_projection);
        let (other_places, kind) = match guide_place.projection[index] {
            ProjectionElem::Field(projected_field, _field_ty) => {
                let other_places = self.expand_field(Some(projected_field.index()), ctxt)?;
                (other_places, ProjectionKind::Field(projected_field))
            }
            ProjectionElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => {
                let range = if from_end {
                    1..min_length + 1
                } else {
                    0..min_length
                };
                assert!(range.contains(&offset));
                let other_places = ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                }
                .other_places(self, ctxt);
                (
                    other_places,
                    ProjectionKind::ConstantIndex(ConstantIndex {
                        offset,
                        min_length,
                        from_end,
                    }),
                )
            }
            ProjectionElem::Deref => {
                let typ = self.ty(ctxt);
                let kind = match typ.ty.kind() {
                    TyKind::Ref(_, _, mutbl) => ProjectionKind::DerefRef(*mutbl),
                    TyKind::RawPtr(_, mutbl) => ProjectionKind::DerefRawPtr(*mutbl),
                    _ if typ.ty.is_box() => ProjectionKind::DerefBox,
                    _ => unreachable!(),
                };
                (Vec::new(), kind)
            }
            ProjectionElem::Index(..)
            | ProjectionElem::Subslice { .. }
            | ProjectionElem::Downcast(..)
            | ProjectionElem::OpaqueCast(..) => (Vec::new(), ProjectionKind::Other),
            _ => todo!(),
        };
        for p in &other_places {
            assert!(
                p.projection.len() == self.projection.len() + 1,
                "expanded place {p:?} is not a direct child of {self:?}",
            );
        }
        Ok(ShallowExpansion::new(
            new_current_place,
            other_places,
            kind,
            ctxt,
        ))
    }

    /// Expands a place `x.f.g` of type struct into a vector of places for
    /// each of the struct's fields `{x.f.g.f, x.f.g.g, x.f.g.h}`. If
    /// `without_field` is not `None`, then omits that field from the final
    /// vector.
    pub fn expand_field<'a>(
        self,
        without_field: Option<usize>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Result<Vec<Self>, PcgError>
    where
        'tcx: 'a,
    {
        let mut places = Vec::new();
        let typ = self.ty(ctxt);
        if !matches!(typ.ty.kind(), TyKind::Adt(..)) {
            assert!(
                typ.variant_index.is_none(),
                "We have assumed that only enums can have variant_index set. Got {typ:?}."
            );
        }
        match typ.ty.kind() {
            TyKind::Adt(def, substs) => {
                let variant = typ
                    .variant_index
                    .map(|i| def.variant(i))
                    .unwrap_or_else(|| def.non_enum_variant());
                if let Some(without_field) = without_field {
                    assert!(without_field < variant.fields.len());
                }
                for (index, field_def) in variant.fields.iter().enumerate() {
                    if Some(index) != without_field {
                        let field = FieldIdx::from_usize(index);
                        let field_place = ctxt.tcx().mk_place_field(
                            self.to_rust_place(ctxt),
                            field,
                            field_def.ty(ctxt.tcx(), substs),
                        );
                        places.push(field_place.into());
                    }
                }
                if without_field.is_some() {
                    assert!(places.len() == variant.fields.len() - 1);
                } else {
                    assert!(places.len() == variant.fields.len());
                }
            }
            TyKind::Tuple(slice) => {
                if let Some(without_field) = without_field {
                    assert!(without_field < slice.len());
                }
                for (index, arg) in slice.iter().enumerate() {
                    if Some(index) != without_field {
                        let field = FieldIdx::from_usize(index);
                        let field_place =
                            ctxt.tcx()
                                .mk_place_field(self.to_rust_place(ctxt), field, arg);
                        places.push(field_place.into());
                    }
                }
                if without_field.is_some() {
                    assert!(places.len() == slice.len() - 1);
                } else {
                    assert!(places.len() == slice.len());
                }
            }
            TyKind::Closure(_, substs) => {
                for (index, subst_ty) in substs.as_closure().upvar_tys().iter().enumerate() {
                    if Some(index) != without_field {
                        let field = FieldIdx::from_usize(index);
                        let field_place =
                            ctxt.tcx()
                                .mk_place_field(self.to_rust_place(ctxt), field, subst_ty);
                        places.push(field_place.into());
                    }
                }
            }
            TyKind::Ref(..) => {
                places.push(ctxt.tcx().mk_place_deref(self.to_rust_place(ctxt)).into());
            }
            TyKind::Alias(..) => {
                return Err(PcgError::unsupported(
                    PcgUnsupportedError::ExpansionOfAliasType,
                ));
            }
            _ => unreachable!("ty={:?} ({self:?})", typ),
        }
        Ok(places)
    }
}

impl<'a, 'tcx: 'a, Ctxt: DebugCtxt + HasCompilerCtxt<'a, 'tcx>> HasValidityCheck<Ctxt>
    for Place<'tcx>
{
    fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
        self.local.check_validity(ctxt)
    }
}

impl<'tcx> Place<'tcx> {
    pub fn ty<'a>(self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> PlaceTy<'tcx>
    where
        'tcx: 'a,
    {
        (*self).ty(ctxt.body(), ctxt.tcx())
    }

    pub fn projects_shared_ref<'a>(self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> bool
    where
        'tcx: 'a,
    {
        self.projects_ty(
            |typ| {
                typ.ty
                    .ref_mutability()
                    .map(|m| m.is_not())
                    .unwrap_or_default()
            },
            ctxt,
        )
        .is_some()
    }

    pub(crate) fn projects_ty<'a>(
        self,
        mut predicate: impl FnMut(PlaceTy<'tcx>) -> bool,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Option<Place<'tcx>>
    where
        'tcx: 'a,
    {
        self.projection_tys(ctxt.ctxt())
            .find(|(typ, _)| predicate(*typ))
            .map(|(_, proj)| {
                let projection = ctxt.tcx().mk_place_elems(proj);
                Self::new(self.local, projection)
            })
    }

    pub(crate) fn projection_tys<'a>(
        self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> impl Iterator<Item = (PlaceTy<'tcx>, &'tcx [PlaceElem<'tcx>])>
    where
        'tcx: 'a,
    {
        let mut typ = PlaceTy::from_ty(ctxt.body().local_decls()[self.local].ty);
        self.projection.iter().enumerate().map(move |(idx, elem)| {
            let ret = (typ, &self.projection[0..idx]);
            typ = typ.projection_ty(ctxt.tcx(), *elem);
            ret
        })
    }
}
