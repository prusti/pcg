use crate::{
    owned_pcg::{RepackGuide, traverse::Traversable},
    utils::data_structures::HashSet,
};
use std::{collections::HashMap, marker::PhantomData};

use derive_more::{Deref, DerefMut};

use crate::{
    utils::place::PlaceExpansion,
    owned_pcg::{
        ExpandedPlace, OwnedExpansion,
        node_data::{Deep, InternalData, Shallow},
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

#[derive(Clone, PartialEq, Eq, Debug, Deref)]
pub struct OwnedPcgInternalNode<'tcx, IData: InternalData<'tcx> = Deep> {
    expansions: HashMap<RepackGuide, OwnedExpansion<'tcx, IData>>,
}

impl<'tcx, IData: InternalData<'tcx>> OwnedPcgInternalNode<'tcx, IData> {
    pub(crate) fn from_expansions(expansions: Vec<OwnedExpansion<'tcx, IData>>) -> Self {
        Self {
            expansions: HashMap::from_iter(expansions.into_iter().map(|e| (e.guide(), e))),
        }
    }

    pub(crate) fn new(expansion: OwnedExpansion<'tcx, IData>) -> Self {
        Self::from_expansions(vec![expansion])
    }

    pub(crate) fn expansions(&self) -> impl Iterator<Item = &OwnedExpansion<'tcx, IData>> {
        self.expansions.iter().map(|(_, e)| e)
    }

    pub(crate) fn expansion(&self, guide: RepackGuide) -> Option<&OwnedExpansion<'tcx, IData>> {
        self.expansions.get(&guide)
    }

    pub(crate) fn expansions_mut(
        &mut self,
    ) -> impl Iterator<Item = &mut OwnedExpansion<'tcx, IData>> {
        self.expansions.iter_mut().map(|(_, e)| e)
    }

    pub(crate) fn expanded_places(&self, place: Place<'tcx>) -> HashSet<ExpandedPlace<'tcx>> {
        self.expansions
            .iter()
            .map(|(_, e)| ExpandedPlace::new(place, e.expansion.without_data()))
            .collect()
    }

    pub(crate) fn insert_expansion(&mut self, expansion: OwnedExpansion<'tcx, IData>) {
        self.expansions.insert(expansion.guide(), expansion);
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
        Self::Internal(OwnedPcgInternalNode::new(OwnedExpansion::new(
            place_expansion,
        )))
    }
}

impl<'tcx> OwnedPcgNode<'tcx> {
    pub(crate) fn owned_capability(&self) -> Option<OwnedCapability> {
        self.as_leaf_node().map(|leaf| leaf.inherent_capability)
    }
}

trait OwnedPcgNodeLike<'tcx> {}
