use std::marker::PhantomData;

use crate::owned_pcg::node::OwnedPcgNode;

pub trait NodeData<'tcx>: Sized {
    type Data: Clone + Eq + std::fmt::Debug;
    type LeafData: Clone + Eq + std::fmt::Debug = ();
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct RealData;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Shallow<T = ()>(PhantomData<T>);

impl<'tcx> NodeData<'tcx> for RealData {
    type Data = OwnedPcgNode<'tcx>;
}

impl<T: Clone + Eq + std::fmt::Debug> NodeData<'_> for Shallow<T> {
    type Data = T;
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct MaterializedData;

impl<'tcx> NodeData<'tcx> for MaterializedData {
    type Data = OwnedPcgNode<'tcx, MaterializedData>;
    type LeafData = ();
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct WithMaterialized;

impl<'tcx> NodeData<'tcx> for WithMaterialized {
    type Data = OwnedPcgNode<'tcx, WithMaterialized>;
    type LeafData = Option<OwnedPcgNode<'tcx, MaterializedData>>;
}
