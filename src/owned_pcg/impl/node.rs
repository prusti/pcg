use std::marker::PhantomData;

use derive_more::{Deref, DerefMut, From};

use crate::{
    owned_pcg::{
        OwnedExpansion,
        node_data::{NodeData, RealData},
    },
    pcg::OwnedCapability,
};

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum OwnedPcgNode<'tcx, Data: NodeData<'tcx> = RealData> {
    Leaf(OwnedPcgLeafNode<'tcx, Data>),
    Internal(OwnedPcgInternalNode<'tcx, Data>),
}

impl<'tcx, IData: NodeData<'tcx>> OwnedPcgNode<'tcx, IData> {
    pub(crate) fn as_internal_mut(&mut self) -> Option<&mut OwnedPcgInternalNode<'tcx, IData>> {
        match self {
            Self::Internal(internal) => Some(&mut *internal),
            Self::Leaf(_) => None,
        }
    }
}

pub struct OwnedPcgLeafNode<'tcx, D: NodeData<'tcx> = RealData> {
    pub(crate) capability: OwnedCapability,
    pub(crate) leaf_data: D::LeafData,
    _marker: PhantomData<&'tcx ()>,
}

impl<'tcx, D: NodeData<'tcx>> Clone for OwnedPcgLeafNode<'tcx, D> {
    fn clone(&self) -> Self {
        Self {
            capability: self.capability,
            leaf_data: self.leaf_data.clone(),
            _marker: PhantomData,
        }
    }
}

impl<'tcx, D: NodeData<'tcx>> Copy for OwnedPcgLeafNode<'tcx, D> where D::LeafData: Copy {}

impl<'tcx, D: NodeData<'tcx>> PartialEq for OwnedPcgLeafNode<'tcx, D> {
    fn eq(&self, other: &Self) -> bool {
        self.capability == other.capability && self.leaf_data == other.leaf_data
    }
}

impl<'tcx, D: NodeData<'tcx>> Eq for OwnedPcgLeafNode<'tcx, D> {}

impl<'tcx, D: NodeData<'tcx>> std::fmt::Debug for OwnedPcgLeafNode<'tcx, D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OwnedPcgLeafNode")
            .field("capability", &self.capability)
            .field("leaf_data", &self.leaf_data)
            .finish()
    }
}

impl OwnedPcgLeafNode<'_> {
    pub(crate) fn new(inherent_capability: OwnedCapability) -> Self {
        Self {
            capability: inherent_capability,
            leaf_data: (),
            _marker: PhantomData,
        }
    }
}

impl<'tcx, D: NodeData<'tcx>> OwnedPcgLeafNode<'tcx, D> {
    pub(crate) fn with_data(inherent_capability: OwnedCapability, leaf_data: D::LeafData) -> Self {
        Self {
            capability: inherent_capability,
            leaf_data,
            _marker: PhantomData,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Deref, From, DerefMut)]
pub struct OwnedPcgInternalNode<'tcx, IData: NodeData<'tcx> = RealData> {
    expansion: Box<OwnedExpansion<'tcx, IData>>,
}

impl<'tcx, IData: NodeData<'tcx>> OwnedPcgInternalNode<'tcx, IData> {
    pub(crate) fn new(expansion: OwnedExpansion<'tcx, IData>) -> Self {
        Self {
            expansion: Box::new(expansion),
        }
    }
}

impl<'tcx, IData: NodeData<'tcx>> OwnedPcgNode<'tcx, IData>
where
    IData::LeafData: Default,
{
    pub(crate) fn leaf(inherent_capability: OwnedCapability) -> Self {
        Self::Leaf(OwnedPcgLeafNode::with_data(
            inherent_capability,
            Default::default(),
        ))
    }
}

impl OwnedPcgNode<'_> {
    pub(crate) fn owned_capability(&self) -> Option<OwnedCapability> {
        self.as_leaf_node().map(|leaf| leaf.capability)
    }
}
