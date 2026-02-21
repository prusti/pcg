use std::marker::PhantomData;

use crate::owned_pcg::{OwnedExpansion, OwnedPcgInternalNode, node::OwnedPcgNode};

pub trait InternalData<'tcx>: Sized  {
    type Data: Clone + Eq + std::fmt::Debug;
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Deep;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DeepRef<'src>(PhantomData<&'src ()>);

impl<'src, 'tcx: 'src> InternalData<'tcx> for DeepRef<'src> {
    type Data = &'src OwnedPcgNode<'tcx>;
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Shallow<T = ()>(PhantomData<T>);

impl<'tcx> InternalData<'tcx> for Deep {
    type Data = OwnedPcgNode<'tcx>;
}

pub(crate) trait FromData<'src, 'tcx, IData: InternalData<'tcx>>:
    InternalData<'tcx>
{
    fn from_data(data: &'src OwnedPcgInternalNode<'tcx, IData>)
    -> OwnedPcgInternalNode<'tcx, Self>;
}

impl<'tcx, T: Clone + Eq + std::fmt::Debug> InternalData<'tcx> for Shallow<T> {
    type Data = T;
}

impl<'src, 'tcx, IData: InternalData<'tcx>> FromData<'src, 'tcx, IData> for Shallow<()> {
    fn from_data(
        data: &'src OwnedPcgInternalNode<'tcx, IData>,
    ) -> OwnedPcgInternalNode<'tcx, Self> {
        OwnedPcgInternalNode::from_expansions(
            data.expansions()
                .map(|e| OwnedExpansion::new(e.expansion.without_data()))
                .collect(),
        )
    }
}

impl<'src, 'tcx: 'src> FromData<'src, 'tcx, Deep> for DeepRef<'src> {
    fn from_data(data: &'src OwnedPcgInternalNode<'tcx>) -> OwnedPcgInternalNode<'tcx, Self> {
        OwnedPcgInternalNode::from_expansions(
            data.expansions()
                .map(|e| OwnedExpansion::new(e.expansion.as_ref()))
                .collect(),
        )
    }
}
