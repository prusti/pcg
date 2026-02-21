use std::marker::PhantomData;

use crate::owned_pcg::{OwnedExpansion, OwnedPcgInternalNode, node::OwnedPcgNode};

pub trait InternalData<'tcx>: Sized {
    type Data: Clone + Eq + std::fmt::Debug;
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Deep;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Shallow<T = ()>(PhantomData<T>);

impl<'tcx> InternalData<'tcx> for Deep {
    type Data = OwnedPcgNode<'tcx>;
}

pub(crate) trait FromDeep<'tcx>: InternalData<'tcx> {
    fn from_deep(deep: &OwnedPcgInternalNode<'tcx>) -> OwnedPcgInternalNode<'tcx, Self>;
}

impl<'tcx, T: Clone + Eq + std::fmt::Debug> InternalData<'tcx> for Shallow<T> {
    type Data = T;
}

impl<'tcx> FromDeep<'tcx> for Shallow<()> {
    fn from_deep(deep: &OwnedPcgInternalNode<'tcx>) -> OwnedPcgInternalNode<'tcx, Self> {
        OwnedPcgInternalNode::from_expansions(
            deep.expansions()
                .map(|e| OwnedExpansion::new(e.expansion.without_data()))
                .collect(),
        )
    }
}

impl<'tcx> FromDeep<'tcx> for Deep {
    fn from_deep(deep: &OwnedPcgInternalNode<'tcx>) -> OwnedPcgInternalNode<'tcx, Self> {
        deep.clone()
    }
}
