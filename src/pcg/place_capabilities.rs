use std::{borrow::Cow, collections::HashMap, marker::PhantomData};

use itertools::Itertools;

use crate::{
    borrow_pcg::{
        borrow_pcg_expansion::BorrowPcgPlaceExpansion,
        edge_data::LabelNodePredicate,
        state::{BorrowStateMutRef, BorrowsStateLike},
        validity_conditions::ValidityConditions,
    },
    pcg::{CapabilityKind, CapabilityLike, PositiveCapability, SymbolicCapability},
    rustc_interface::middle::mir,
    utils::{
        CompilerCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, HasPlace, Place,
        display::{DebugLines, DisplayWithCompilerCtxt},
        validity::HasValidityCheck,
    },
};

mod private {
    use crate::{pcg::SymbolicCapability, rustc_interface::middle::mir};

    use crate::utils::{HasCompilerCtxt, Place, PlaceLike, PrefixRelation};

    pub trait PlaceCapabilitiesReader<'tcx, C = SymbolicCapability, P: Copy = Place<'tcx>> {
        fn get<Ctxt>(&self, place: P, ctxt: Ctxt) -> Option<C>;

        fn iter(&self) -> impl Iterator<Item = (P, C)> + '_;

        fn capabilities_for_strict_postfixes_of<'slf>(
            &'slf self,
            place: P,
        ) -> impl Iterator<Item = (P, C)> + 'slf
        where
            'tcx: 'slf,
            C: 'slf,
            P: 'slf + PrefixRelation,
        {
            self.iter().filter_map(move |(p, c)| {
                if place.is_strict_prefix_of(p) {
                    Some((p, c))
                } else {
                    None
                }
            })
        }
    }

    pub trait PlaceCapabilitiesInterface<'tcx, C = SymbolicCapability, P: Copy = Place<'tcx>>:
        PlaceCapabilitiesReader<'tcx, C, P>
    where
        P: Copy + Eq + std::hash::Hash,
    {
        fn insert<Ctxt>(&mut self, place: P, capability: impl Into<C>, ctxt: Ctxt) -> bool;

        fn remove<Ctxt>(&mut self, place: P, ctxt: Ctxt) -> Option<C>;

        fn retain(&mut self, predicate: impl Fn(P, C) -> bool);

        fn iter_mut<'slf>(&'slf mut self) -> impl Iterator<Item = (&'slf P, &'slf mut C)> + 'slf
        where
            C: 'slf,
            P: 'slf,
            'tcx: 'slf;

        fn owned_capabilities<'a: 'slf, 'slf, Ctxt: HasCompilerCtxt<'a, 'tcx> + 'slf>(
            &'slf mut self,
            local: mir::Local,
            ctxt: Ctxt,
        ) -> impl Iterator<Item = (P, &'slf mut C)> + 'slf
        where
            C: 'static,
            'tcx: 'a,
            P: 'slf + PlaceLike<'tcx, Ctxt>,
        {
            self.iter_mut().filter_map(move |(place, capability)| {
                if place.local() == local && place.is_owned(ctxt) {
                    Some((*place, capability))
                } else {
                    None
                }
            })
        }

        fn remove_all_postfixes(&mut self, place: P, _ctxt: impl HasCompilerCtxt<'_, 'tcx>)
        where
            P: PrefixRelation,
        {
            self.retain(|p, _| !place.is_prefix_of(p));
        }
    }
}
pub(crate) use private::*;

impl<'tcx, C, P> PlaceCapabilitiesReader<'tcx, C, P> for PlaceCapabilities<'tcx, C, P>
where
    P: Copy + Eq + std::hash::Hash,
    C: Copy,
{
    fn get<Ctxt>(&self, place: P, _ctxt: Ctxt) -> Option<C> {
        self.map.get(&place).copied()
    }

    fn iter(&self) -> impl Iterator<Item = (P, C)> + '_ {
        self.map.iter().map(|(k, v)| (*k, *v))
    }
}

impl<'tcx, C, P> PlaceCapabilitiesInterface<'tcx, C, P> for PlaceCapabilities<'tcx, C, P>
where
    P: Copy + Eq + std::hash::Hash,
    C: Copy,
{
    fn insert<Ctxt>(&mut self, place: P, capability: impl Into<C>, _ctxt: Ctxt) -> bool {
        self.map.insert(place, capability.into()).is_some()
    }

    fn remove<Ctxt>(&mut self, place: P, _ctxt: Ctxt) -> Option<C> {
        self.map.remove(&place)
    }

    fn retain(&mut self, predicate: impl Fn(P, C) -> bool) {
        self.map.retain(|place, cap| predicate(*place, *cap));
    }

    fn iter_mut<'slf>(&'slf mut self) -> impl Iterator<Item = (&'slf P, &'slf mut C)> + 'slf
    where
        C: 'slf,
        P: 'slf,
        'tcx: 'slf,
    {
        self.map.iter_mut()
    }
}

#[allow(dead_code)]
pub(crate) struct ConditionMap<V>(HashMap<V, ValidityConditions>);

#[allow(dead_code)]
pub(crate) type ConditionalCapabilities<'tcx> =
    PlaceCapabilities<'tcx, ConditionMap<CapabilityKind>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlaceCapabilities<'tcx, C = CapabilityKind, P = Place<'tcx>>
where
    P: Eq + std::hash::Hash,
{
    pub(crate) map: HashMap<P, C>,
    pub(crate) _marker: PhantomData<&'tcx ()>,
}

impl<C, P> Default for PlaceCapabilities<'_, C, P>
where
    P: Eq + std::hash::Hash,
{
    fn default() -> Self {
        Self {
            map: HashMap::default(),
            _marker: PhantomData,
        }
    }
}

pub(crate) type SymbolicPlaceCapabilities<'tcx> = PlaceCapabilities<'tcx, SymbolicCapability>;

impl<'a, 'tcx: 'a> SymbolicPlaceCapabilities<'tcx> {
    pub(crate) fn to_concrete(
        &self,
        ctxt: impl HasCompilerCtxt<'_, 'tcx>,
    ) -> PlaceCapabilities<'tcx> {
        let mut concrete = PlaceCapabilities::default();
        for (place, cap) in self.iter() {
            concrete.insert(place, cap.expect_concrete(), ctxt);
        }
        concrete
    }

    pub(crate) fn update_for_deref<Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
        &mut self,
        ref_place: Place<'tcx>,
        capability: PositiveCapability,
        ctxt: Ctxt,
    ) -> bool {
        if capability.is_read() || ref_place.is_shared_ref(ctxt.bc_ctxt()) {
            self.insert(
                ref_place,
                SymbolicCapability::Concrete(CapabilityKind::Read),
                ctxt,
            );
            self.insert(
                ref_place.project_deref(ctxt.bc_ctxt()),
                SymbolicCapability::Concrete(CapabilityKind::Read),
                ctxt,
            );
        } else {
            self.insert(
                ref_place,
                SymbolicCapability::Concrete(CapabilityKind::Write),
                ctxt,
            );
            self.insert(
                ref_place.project_deref(ctxt.bc_ctxt()),
                SymbolicCapability::Concrete(CapabilityKind::Exclusive),
                ctxt,
            );
        }
        true
    }

    pub(crate) fn update_for_expansion<Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
        &mut self,
        expansion: &BorrowPcgPlaceExpansion<'tcx>,
        block_type: BlockType,
        ctxt: Ctxt,
    ) -> bool {
        let mut changed = false;
        let base = expansion.base;
        let base_capability = self.get(base.place(), ctxt);
        let expanded_capability = if let Some(capability) = base_capability {
            let concrete_cap = capability.expect_concrete().into_positive().unwrap();
            let expanded = block_type.expansion_capability(base.place(), concrete_cap, ctxt);
            SymbolicCapability::Concrete(expanded.into())
        } else {
            return true;
        };

        changed |= self.update_capabilities_for_block_of_place(base.place(), block_type, ctxt);

        for p in &expansion.expansion {
            changed |= self.insert(p.place(), expanded_capability, ctxt);
        }
        changed
    }

    pub(crate) fn update_capabilities_for_block_of_place<Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
        &mut self,
        blocked_place: Place<'tcx>,
        block_type: BlockType,
        ctxt: Ctxt,
    ) -> bool {
        let retained_capability = block_type.blocked_place_maximum_retained_capability();
        self.insert(blocked_place, retained_capability, ctxt)
    }
}

impl<'a, 'tcx> HasValidityCheck<CompilerCtxt<'a, 'tcx>> for PlaceCapabilities<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> Result<(), String> {
        for (place, cap) in self.iter() {
            if place.projects_shared_ref(ctxt) && !cap.is_read() {
                return Err(format!(
                    "Place {} projects a shared ref, but has capability {:?}",
                    place.display_string(ctxt),
                    cap
                ));
            }
        }
        for (local, _) in ctxt.body().local_decls.iter_enumerated() {
            let caps_from_local = self
                .iter()
                .filter(|(place, _)| place.local == local)
                .sorted_by_key(|(place, _)| place.projection.len())
                .collect_vec();
            if caps_from_local.is_empty() {
                continue;
            }
            fn allowed_child_cap<'tcx>(
                parent_place: Place<'tcx>,
                parent_cap: CapabilityKind,
                child_cap: CapabilityKind,
                ctxt: CompilerCtxt<'_, 'tcx>,
            ) -> bool {
                match (parent_cap, child_cap) {
                    (CapabilityKind::Write, _) if parent_place.ref_mutability(ctxt).is_some() => {
                        true
                    }
                    (CapabilityKind::Read, CapabilityKind::Read)
                    | (CapabilityKind::None(()), _) => true,
                    _ => false,
                }
            }
            for i in 0..caps_from_local.len() - 1 {
                let (place, parent_cap) = caps_from_local[i];
                for (other_place, other_cap) in caps_from_local.iter().skip(i + 1) {
                    let (other_place, other_cap) = (*other_place, *other_cap);
                    if place.is_prefix_of(other_place)
                        && !allowed_child_cap(place, parent_cap, other_cap, ctxt)
                    {
                        return Err(format!(
                            "Place ({}: {}) with capability {:?} has a child {} with capability {:?} which is not allowed",
                            place.display_string(ctxt),
                            place.ty(ctxt).ty,
                            parent_cap,
                            other_place.display_string(ctxt),
                            other_cap
                        ));
                    }
                }
            }
        }
        Ok(())
    }
}

impl<'tcx> DebugLines<CompilerCtxt<'_, 'tcx>> for SymbolicPlaceCapabilities<'tcx> {
    fn debug_lines(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Vec<Cow<'static, str>> {
        self.iter()
            .map(|(node, capability)| {
                Cow::Owned(format!(
                    "{}: {:?}",
                    node.display_string(ctxt),
                    capability.expect_concrete()
                ))
            })
            .sorted()
            .collect()
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum BlockType {
    /// Derefing a mutable reference, *not* in the context of a two-phase borrow
    /// of otherwise just for read. The reference will be downgraded to w.
    DerefMutRefForExclusive,
    /// Dereferencing a mutable reference that is stored under a shared borrow
    DerefMutRefUnderSharedRef,
    DerefSharedRef,
    Read,
    Other,
}

impl BlockType {
    pub(crate) fn blocked_place_maximum_retained_capability(self) -> CapabilityKind {
        match self {
            BlockType::DerefSharedRef => CapabilityKind::Exclusive,
            BlockType::DerefMutRefForExclusive => CapabilityKind::Write,
            BlockType::DerefMutRefUnderSharedRef | BlockType::Read => CapabilityKind::Read,
            BlockType::Other => CapabilityKind::None(()),
        }
    }
    pub(crate) fn expansion_capability<'tcx>(
        self,
        _blocked_place: Place<'tcx>,
        blocked_capability: PositiveCapability,
        _ctxt: impl HasCompilerCtxt<'_, 'tcx>,
    ) -> PositiveCapability {
        match self {
            BlockType::DerefMutRefUnderSharedRef | BlockType::Read | BlockType::DerefSharedRef => {
                PositiveCapability::Read
            }
            BlockType::DerefMutRefForExclusive => PositiveCapability::Exclusive,
            BlockType::Other => blocked_capability,
        }
    }
}

impl<'tcx, C: CapabilityLike> PlaceCapabilities<'tcx, C>
where
    Self: PlaceCapabilitiesInterface<'tcx, C>,
{
    pub(crate) fn regain_loaned_capability<'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
        &mut self,
        place: Place<'tcx>,
        capability: C,
        mut borrows: BorrowStateMutRef<'_, 'tcx>,
        ctxt: Ctxt,
    ) where
        'tcx: 'a,
        C: 'static,
    {
        self.insert((*place).into(), capability, ctxt);
        if capability == PositiveCapability::Exclusive.into() {
            borrows.label_lifetime_projections(
                &LabelNodePredicate::all_future_postfixes(place),
                None,
                ctxt.bc_ctxt(),
            );
        }
    }

    pub(crate) fn remove_all_for_local(
        &mut self,
        local: mir::Local,
        _ctxt: impl HasCompilerCtxt<'_, 'tcx>,
    ) {
        self.map.retain(|place, _| place.place().local != local);
    }
}

impl<C: CapabilityLike<Minimum = C>, P> PlaceCapabilities<'_, C, P>
where
    P: Copy + Eq + std::hash::Hash,
{
    pub(crate) fn join<Ctxt: Copy>(&mut self, other: &Self, ctxt: Ctxt) -> bool
    where
        C: 'static,
    {
        let mut changed = false;
        self.map.retain(|place, _| other.map.contains_key(place));
        for (place, other_capability) in &other.map {
            let place = *place;
            let other_capability = *other_capability;
            if let Some(self_capability) = self.map.get(&place) {
                let c = self_capability.minimum(other_capability, ctxt);
                changed |= self.map.insert(place, c) != Some(c);
            }
        }
        changed
    }
}

impl<'tcx, C: Copy + PartialEq> PlaceCapabilities<'tcx, C> {
    pub(crate) fn uniform_capability<'a>(
        &self,
        mut places: impl Iterator<Item = Place<'tcx>>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Option<C>
    where
        'tcx: 'a,
    {
        let cap = self.get(places.next()?, ctxt)?;
        for p in places {
            if self.get(p, ctxt) != Some(cap) {
                return None;
            }
        }
        Some(cap)
    }

    pub(crate) fn remove_all_strict_postfixes<'a>(
        &mut self,
        place: Place<'tcx>,
        _ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) where
        'tcx: 'a,
    {
        self.map.retain(|p, _| !place.is_strict_prefix_of(*p));
    }
}

impl<'tcx> PlaceCapabilities<'tcx, SymbolicCapability> {
    #[must_use]
    pub fn is_exclusive(&self, place: Place<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.get(place, ctxt)
            .is_some_and(|c| c.expect_concrete() == PositiveCapability::Exclusive)
    }
}
