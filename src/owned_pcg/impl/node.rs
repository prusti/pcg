use std::marker::PhantomData;
use crate::utils::data_structures::HashSet;

use derive_more::{Deref, DerefMut};

use crate::{
    borrow_pcg::borrow_pcg_expansion::PlaceExpansion,
    owned_pcg::{
        ExpandedPlace, OwnedExpansion,
        node_data::{Deep, InternalData, Shallow},
        traverse::All,
    },
    pcg::OwnedCapability,
    utils::{HasCompilerCtxt, Place},
};

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum OwnedPcgNode<'tcx, IData: InternalData<'tcx> = Deep> {
    Leaf(OwnedPcgLeafNode<'tcx>),
    Internal(OwnedPcgInternalNode<'tcx, IData>),
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct OwnedPcgLeafNode<'tcx> {
    pub(crate) inherent_capability: OwnedCapability,
    _marker: PhantomData<&'tcx ()>,
}

impl<'tcx> OwnedPcgLeafNode<'tcx> {
    pub(crate) fn new(inherent_capability: OwnedCapability) -> Self {
        Self {
            inherent_capability,
            _marker: PhantomData,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Deref, DerefMut)]
pub struct OwnedPcgInternalNode<'tcx, IData: InternalData<'tcx> = Deep> {
    pub(crate) expansions: Vec<OwnedExpansion<'tcx, IData>>,
}

impl<'tcx, IData: InternalData<'tcx>> OwnedPcgInternalNode<'tcx, IData> {
    pub(crate) fn new(expansions: Vec<OwnedExpansion<'tcx, IData>>) -> Self {
        Self { expansions }
    }

    pub(crate) fn expansions(&self) -> &Vec<OwnedExpansion<'tcx, IData>> {
        &self.expansions
    }

    pub(crate) fn expanded_places(&self, place: Place<'tcx>) -> HashSet<ExpandedPlace<'tcx>> {
        self.expansions
            .iter()
            .map(|e| ExpandedPlace::new(place, e.expansion.without_data()))
            .collect()
    }

}

pub(crate) type ShallowOwnedNode<'tcx> = OwnedPcgNode<'tcx, Shallow>;

impl<'tcx, IData: InternalData<'tcx>> OwnedPcgNode<'tcx, IData> {
    pub(crate) fn is_leaf(&self) -> bool {
        matches!(self, Self::Leaf(_))
    }
    pub(crate) fn leaf(inherent_capability: OwnedCapability) -> Self {
        Self::Leaf(OwnedPcgLeafNode::new(inherent_capability))
    }
    pub(crate) fn internal(place_expansion: PlaceExpansion<'tcx, IData::Data>) -> Self {
        Self::Internal(OwnedPcgInternalNode::new(vec![OwnedExpansion::new(
            place_expansion,
        )]))
    }
}

impl<'tcx> OwnedPcgNode<'tcx> {
    pub(crate) fn is_fully_initialized<'a>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        self.traverse(
            place,
            &mut All(Box::new(|leaf| leaf.inherent_capability.is_deep())),
            ctxt,
        )
    }
}
