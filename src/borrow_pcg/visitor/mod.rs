use std::ops::ControlFlow;

use derive_more::{Deref, DerefMut};

use crate::{
    rustc_interface::{
        ast::Mutability,
        index::IndexVec,
        middle::ty::{self, TypeSuperVisitable, TypeVisitable, TypeVisitor},
    },
    utils::data_structures::{HashMap, HashSet},
};

use super::region_projection::{PcgRegion, RegionIdx};

trait Extractor<'tcx> {
    fn pre_visit_ty(&mut self, ty: ty::Ty<'tcx>) -> ControlFlow<(), ()>;
    fn push_mutability(&mut self, mutability: Mutability);
    fn pop_mutability(&mut self);
    fn visit_adt(&mut self, adt_def: ty::AdtDef<'tcx>, args: ty::GenericArgsRef<'tcx>);
    fn visit_pcg_region(&mut self, region: PcgRegion<'tcx>);
}

struct RegionMutabilityExtractor<'tcx> {
    seen_tys: HashSet<(Mutability, ty::Ty<'tcx>)>,
    mutability: Vec<Mutability>,
    lifetimes: HashMap<PcgRegion<'tcx>, Mutability>,
    ty: ty::Ty<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
}

struct RegionExtractor<'tcx> {
    lifetimes: IndexVec<RegionIdx, PcgRegion<'tcx>>,
}

#[derive(Deref, DerefMut)]
struct ExtractWrapper<'inner, E>(&'inner mut E);

impl<'tcx> Extractor<'tcx> for RegionExtractor<'tcx> {
    fn pre_visit_ty(&mut self, _ty: ty::Ty<'tcx>) -> ControlFlow<(), ()> {
        ControlFlow::Continue(())
    }
    fn push_mutability(&mut self, _mutability: Mutability) {}
    fn pop_mutability(&mut self) {}
    fn visit_adt(&mut self, _adt_def: ty::AdtDef<'tcx>, args: ty::GenericArgsRef<'tcx>) {
        args.visit_with(&mut ExtractWrapper(self));
    }
    fn visit_pcg_region(&mut self, region: PcgRegion<'tcx>) {
        if !self.lifetimes.iter().any(|r| *r == region) {
            self.lifetimes.push(region);
        }
    }
}

impl<'tcx> Extractor<'tcx> for RegionMutabilityExtractor<'tcx> {
    fn pre_visit_ty(&mut self, ty: ty::Ty<'tcx>) -> ControlFlow<(), ()> {
        let curr_mutability = self.mutability.last().copied().unwrap_or(Mutability::Mut);
        if self.seen_tys.contains(&(curr_mutability, ty)) {
            ControlFlow::Break(())
        } else {
            self.seen_tys.insert((curr_mutability, ty));
            ControlFlow::Continue(())
        }
    }
    fn push_mutability(&mut self, mutability: Mutability) {
        self.mutability.push(mutability);
    }
    fn pop_mutability(&mut self) {
        self.mutability.pop();
    }
    fn visit_adt(&mut self, adt_def: ty::AdtDef<'tcx>, args: ty::GenericArgsRef<'tcx>) {
        tracing::warn!("!Visiting adt {:?} args {:?}", adt_def, args);
        let fields = adt_def.all_fields().collect::<Vec<_>>();
        tracing::warn!("Fields {:?}", fields);
        tracing::warn!("!!Visiting adt {:?}", adt_def);
        for field in adt_def.all_fields() {
            tracing::warn!("Visiting field {:?}", field);
            let tcx = self.tcx;
            ExtractWrapper(self).visit_ty(field.ty(tcx, args));
        }
        args.visit_with(&mut ExtractWrapper(self));
    }

    fn visit_pcg_region(&mut self, region: PcgRegion<'tcx>) {
        let mutability = self.mutability.last().copied().unwrap_or(Mutability::Mut);
        let entry = self.lifetimes.get_mut(&region);
        match entry {
            Some(mutbl) => {
                if mutability == Mutability::Mut {
                    *mutbl = Mutability::Mut;
                }
            }
            None => {
                self.lifetimes.insert(region, mutability);
            }
        }
    }
}

impl<'inner, 'tcx, E: Extractor<'tcx>> TypeVisitor<ty::TyCtxt<'tcx>> for ExtractWrapper<'inner, E> {
    fn visit_ty(&mut self, ty: ty::Ty<'tcx>) {
        if let ControlFlow::Break(()) = self.pre_visit_ty(ty) {
            return;
        }
        match ty.kind() {
            ty::TyKind::Dynamic(_, region, ..) => {
                // TODO: predicates?
                self.visit_region(*region);
            }
            //  TODO: Justify why function pointers are ignored
            ty::TyKind::FnPtr(_, _) => {}
            ty::TyKind::Closure(_, args) => {
                let closure_args = args.as_closure();
                let upvar_tys = closure_args.upvar_tys();
                for ty in upvar_tys {
                    self.visit_ty(ty);
                }
            }
            ty::TyKind::Ref(region, ty, mutbl) => {
                self.push_mutability(*mutbl);
                self.visit_region(*region);
                self.visit_ty(*ty);
                self.pop_mutability();
            }
            ty::TyKind::Adt(adt_def, args) => {
                self.visit_adt(*adt_def, args);
            }
            _ => {
                ty.super_visit_with(self);
            }
        }
    }
    fn visit_region(&mut self, rr: ty::Region<'tcx>) {
        self.visit_pcg_region(rr.into());
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
/// T<'c, 'd> will return the same list of regions will return `['a, 'b]` and
/// `['c, 'd]` respectively. This enables substitution of regions to handle
/// moves in the PCG e.g for the statement `let x: T<'a, 'b> = move c: T<'c,
/// 'd>`.
pub(crate) fn extract_regions(ty: ty::Ty<'_>) -> IndexVec<RegionIdx, PcgRegion<'_>> {
    let mut visitor = RegionExtractor {
        lifetimes: IndexVec::default(),
    };
    ty.visit_with(&mut ExtractWrapper(&mut visitor));
    visitor.lifetimes
}

pub(crate) fn region_mutability<'tcx>(
    ty: ty::Ty<'tcx>,
    region: PcgRegion<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
) -> Mutability {
    let mut visitor = RegionMutabilityExtractor {
        seen_tys: HashSet::default(),
        mutability: vec![],
        lifetimes: HashMap::default(),
        ty,
        tcx,
    };
    ty.visit_with(&mut ExtractWrapper(&mut visitor));
    visitor.lifetimes.get(&region).copied().unwrap_or_else(|| {
        panic!(
            "No mutability found for region {:?} in type {:?}",
            region, ty
        );
    })
}
