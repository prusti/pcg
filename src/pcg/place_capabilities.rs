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
    use crate::pcg::CapabilityKind;
    use crate::{pcg::SymbolicCapability, rustc_interface::middle::mir};

    use crate::utils::{HasCompilerCtxt, Place, PlaceLike, PrefixRelation};

    pub trait PlaceCapabilitiesReader<'tcx, Ctxt, C = CapabilityKind, P: Copy = Place<'tcx>> {
        fn get(&self, place: P, ctxt: Ctxt) -> C;
        fn uniform_capability(&self, mut places: impl Iterator<Item = P>, ctxt: Ctxt) -> Option<C>
        where
            C: PartialEq,
            Ctxt: Copy,
        {
            let place = places.next()?;
            let cap = self.get(place, ctxt);
            for p in places {
                if self.get(p, ctxt) != cap {
                    return None;
                }
            }
            Some(cap)
        }
    }
}
pub(crate) use private::*;

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

impl<'tcx, Ctxt> PlaceCapabilitiesReader<'tcx, Ctxt> for PlaceCapabilities<'tcx> {
    fn get(&self, place: Place<'tcx>, ctxt: Ctxt) -> CapabilityKind {
        self.map
            .get(&place)
            .copied()
            .unwrap_or(CapabilityKind::None(()))
    }
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
