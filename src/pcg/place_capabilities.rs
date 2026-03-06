use std::{collections::HashMap, marker::PhantomData};

use crate::{
    borrow_pcg::validity_conditions::ValidityConditions, pcg::CapabilityKind, utils::Place,
};

mod private {
    use crate::pcg::CapabilityKind;

    use crate::utils::Place;

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
    fn get(&self, place: Place<'tcx>, _ctxt: Ctxt) -> CapabilityKind {
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
}
