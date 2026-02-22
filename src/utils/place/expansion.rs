use std::collections::BTreeMap;

use derive_more::From;
use itertools::Itertools;

use crate::r#loop::PlaceUsageType;
use crate::owned_pcg::RepackGuide;
use crate::pcg::PositiveCapability;
use crate::pcg::obtain::ObtainType;
use crate::pcg::place_capabilities::BlockType;
use crate::utils::corrected::CorrectedPlace;
use crate::utils::{HasCompilerCtxt, Place};
use crate::{
    rustc_interface::{
        FieldIdx,
        middle::{
            mir::{self, PlaceElem},
            ty,
        },
    },
    utils::{CompilerCtxt, validity::HasValidityCheck},
};

/// The projections resulting from an expansion of a place.
///
/// This representation is preferred to a `Vec<PlaceElem>` because it ensures
/// it enables a more reasonable notion of equality between expansions. Directly
/// storing the place elements in a `Vec` could lead to different representations
/// for the same expansion, e.g. `{*x.f.a, *x.f.b}` and `{*x.f.b, *x.f.a}`.
#[derive(PartialEq, Eq, Clone, Debug, Hash, From)]
pub enum PlaceExpansion<'tcx, D = ()> {
    /// Fields from e.g. a struct or tuple, e.g. `{*x.f} -> {*x.f.a, *x.f.b}`
    /// Note that for region projections, not every field of the base type may
    /// be included. For example consider the following:
    /// ```ignore
    /// struct S<'a, 'b> { x: &'a mut i32, y: &'b mut i32 }
    ///
    /// let s: S<'a, 'b> = S { x: &mut 1, y: &mut 2 };
    /// ```
    /// The projection of `s↓'a` contains only `{s.x↓'a}` because nothing under
    /// `'a` is accessible via `s.y`.
    Fields(BTreeMap<FieldIdx, (ty::Ty<'tcx>, D)>),
    /// See [`PlaceElem::Deref`]
    Deref(D),
    Guided(RepackGuide<mir::Local, D, !>),
}

impl<'a, 'tcx> HasValidityCheck<CompilerCtxt<'a, 'tcx>> for PlaceExpansion<'tcx> {
    fn check_validity(&self, _ctxt: CompilerCtxt<'a, 'tcx>) -> Result<(), String> {
        Ok(())
    }
}

impl<'tcx, D: std::fmt::Debug> std::ops::Index<mir::PlaceElem<'tcx>> for PlaceExpansion<'tcx, D> {
    type Output = D;

    fn index(&self, index: mir::PlaceElem<'tcx>) -> &Self::Output {
        self.elems_data()
            .iter()
            .find(|(elem, _)| *elem == index)
            .unwrap_or_else(|| panic!("Index {:?} not found in PlaceExpansion {:?}", index, self))
            .1
            .unwrap()
    }
}

impl<'tcx> PlaceExpansion<'tcx> {
    pub(crate) fn elems(&self) -> Vec<PlaceElem<'tcx>> {
        self.map_elems_data(|_| (), &|_| ())
            .iter()
            .map(|(elem, _)| (*elem).into())
            .collect()
    }
    pub(crate) fn fields(map: BTreeMap<FieldIdx, ty::Ty<'tcx>>) -> Self {
        PlaceExpansion::Fields(map.into_iter().map(|(idx, ty)| (idx, (ty, ()))).collect())
    }
    pub(crate) fn deref() -> Self {
        PlaceExpansion::Deref(())
    }
    pub(crate) fn is_enum_expansion(&self) -> bool {
        matches!(self, PlaceExpansion::Guided(RepackGuide::Downcast(_, _)))
    }

    pub(crate) fn is_deref(&self) -> bool {
        matches!(self, PlaceExpansion::Deref(_))
    }

    pub(crate) fn block_type<'a>(
        &self,
        base_place: Place<'tcx>,
        obtain_type: ObtainType,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> BlockType
    where
        'tcx: 'a,
    {
        if matches!(
            obtain_type,
            ObtainType::Capability(PositiveCapability::Read)
                | ObtainType::TwoPhaseExpand
                | ObtainType::LoopInvariant {
                    usage_type: PlaceUsageType::Read,
                    ..
                }
        ) {
            BlockType::Read
        } else if self.is_deref() {
            if base_place.is_shared_ref(ctxt) {
                BlockType::DerefSharedRef
            } else if base_place.is_mut_ref(ctxt) {
                if base_place.projects_shared_ref(ctxt) {
                    BlockType::DerefMutRefUnderSharedRef
                } else {
                    BlockType::DerefMutRefForExclusive
                }
            } else {
                BlockType::Other
            }
        } else {
            BlockType::Other
        }
    }

    pub(crate) fn from_places<'a>(
        places: Vec<Place<'tcx>>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Self
    where
        'tcx: 'a,
    {
        let mut fields = BTreeMap::new();

        for place in places {
            let corrected_place = CorrectedPlace::new(place, ctxt);
            let last_projection = corrected_place.last_projection();
            if let Some(elem) = last_projection {
                match *elem {
                    PlaceElem::Field(field_idx, ty) => {
                        fields.insert(field_idx, ty);
                    }
                    PlaceElem::Deref => return PlaceExpansion::deref(),
                    other => {
                        let repack_guide: RepackGuide = other.into();
                        return PlaceExpansion::Guided(repack_guide.as_non_default().unwrap());
                    }
                }
            }
        }

        if fields.is_empty() {
            unreachable!()
        } else {
            PlaceExpansion::fields(fields)
        }
    }
}

impl<'tcx, D> PlaceExpansion<'tcx, D> {
    pub(crate) fn without_data(&self) -> PlaceExpansion<'tcx, ()> {
        self.map_data(|_| ())
    }

    pub(crate) fn as_ref<'slf>(&'slf self) -> PlaceExpansion<'tcx, &'slf D> {
        self.map_data(|d| d)
    }

    pub(crate) fn guide(&self) -> RepackGuide {
        match self.required_guide() {
            Some(guide) => guide.without_data().into(),
            None => RepackGuide::Default(()),
        }
    }

    pub(crate) fn required_guide(&self) -> Option<&RepackGuide<mir::Local, D, !>> {
        match self {
            PlaceExpansion::Guided(guide) => Some(guide),
            _ => None,
        }
    }

    pub(crate) fn elems_data<'slf>(&'slf self) -> Vec<(PlaceElem<'tcx>, Option<&'slf D>)> {
        self.map_elems_data(|d| Some(d), &|_| None)
    }

    pub(crate) fn elems_data_mut<'slf>(
        &'slf mut self,
    ) -> Vec<(PlaceElem<'tcx>, Option<&'slf mut D>)> {
        match self {
            PlaceExpansion::Fields(fields) => fields
                .into_iter()
                .sorted_by_key(|(idx, _)| *idx)
                .map(|(idx, (ty, data))| (PlaceElem::Field(*idx, *ty), Some(data)))
                .collect(),
            PlaceExpansion::Deref(data) => vec![(PlaceElem::Deref, Some(data))],
            PlaceExpansion::Guided(RepackGuide::ConstantIndex(c, data)) => {
                let mut elems = vec![((*c).into(), Some(data))];
                elems.extend(c.other_elems().iter().map(|e| ((*e).into(), None)));
                elems
            }
            PlaceExpansion::Guided(guided) => {
                let (elem, data) = guided.elem_data_mut();
                vec![(elem, Some(data))]
            }
        }
    }

    pub(crate) fn map_data<'slf, R>(&'slf self, f: impl Fn(&'slf D) -> R) -> PlaceExpansion<'tcx, R>
    where
        D: 'slf,
        'tcx: 'slf,
    {
        match self {
            PlaceExpansion::Fields(fields) => PlaceExpansion::Fields(
                fields
                    .into_iter()
                    .map(|(idx, (ty, data))| (*idx, (*ty, f(data))))
                    .collect(),
            ),
            PlaceExpansion::Deref(data) => PlaceExpansion::Deref(f(data)),
            PlaceExpansion::Guided(guided) => PlaceExpansion::Guided(guided.map_data(f)),
        }
    }

    pub(crate) fn try_map_data<'slf, R>(
        &'slf self,
        f: impl Fn(&'slf D) -> Option<R>,
    ) -> Option<PlaceExpansion<'tcx, R>> {
        match self {
            PlaceExpansion::Fields(fields) => {
                let mut new_fields = BTreeMap::new();
                for (field_idx, (ty, data)) in fields.iter() {
                    let new_data = f(data)?;
                    new_fields.insert(*field_idx, (*ty, new_data));
                }
                Some(PlaceExpansion::Fields(new_fields))
            }
            PlaceExpansion::Deref(data) => Some(PlaceExpansion::Deref(f(data)?)),
            PlaceExpansion::Guided(guided) => Some(PlaceExpansion::Guided(guided.try_map_data(f)?)),
        }
    }

    pub(crate) fn map_elems_data<'slf, R>(
        &'slf self,
        f: impl Fn(&'slf D) -> R,
        default: impl Fn(&'slf D) -> R,
    ) -> Vec<(PlaceElem<'tcx>, R)> {
        match self {
            PlaceExpansion::Fields(fields) => fields
                .iter()
                .sorted_by_key(|(idx, _)| *idx)
                .map(|(idx, (ty, data))| (PlaceElem::Field(*idx, *ty), f(data)))
                .collect(),
            PlaceExpansion::Deref(data) => vec![(PlaceElem::Deref, f(data))],
            PlaceExpansion::Guided(RepackGuide::ConstantIndex(c, data)) => {
                let mut elems = vec![((*c).into(), f(data))];
                elems.extend(c.other_elems().iter().map(|e| ((*e).into(), default(data))));
                elems
            }
            PlaceExpansion::Guided(guided) => {
                let (elem, data) = guided.elem_data();
                vec![(elem, f(data))]
            }
        }
    }
}

impl<'tcx> Place<'tcx> {
    pub(crate) fn expansion<'a>(
        self,
        guide: RepackGuide,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> PlaceExpansion<'tcx>
    where
        'tcx: 'a,
    {
        if let Some(guide) = guide.as_non_default() {
            guide.into()
        } else if self.ty(ctxt).ty.is_box() {
            PlaceExpansion::deref()
        } else {
            match self.ty(ctxt).ty.kind() {
                ty::TyKind::Adt(adt_def, substs) => {
                    let variant = match self.ty(ctxt).variant_index {
                        Some(v) => adt_def.variant(v),
                        None => adt_def.non_enum_variant(),
                    };
                    PlaceExpansion::fields(
                        variant
                            .fields
                            .iter()
                            .enumerate()
                            .map(|(i, field)| (i.into(), field.ty(ctxt.tcx(), substs)))
                            .collect(),
                    )
                }
                ty::TyKind::Tuple(tys) => PlaceExpansion::fields(
                    tys.iter()
                        .enumerate()
                        .map(|(i, ty)| (i.into(), ty))
                        .collect(),
                ),
                _ => unreachable!("Unexpected type: {:?}", self.ty(ctxt).ty),
            }
        }
    }
}
