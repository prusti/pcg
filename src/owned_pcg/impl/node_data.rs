use std::marker::PhantomData;

use crate::owned_pcg::{OwnedExpansion, OwnedPcgInternalNode, node::OwnedPcgNode};

pub trait InternalData<'tcx>: Sized {
    type Data<'src>: Clone + Eq + std::fmt::Debug where 'tcx: 'src;
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Deep;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DeepRef;

impl<'tcx> InternalData<'tcx> for DeepRef {
    type Data<'src> = &'src OwnedPcgNode<'tcx> where 'tcx: 'src;
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Shallow<T = ()>(PhantomData<T>);

impl<'tcx> InternalData<'tcx> for Deep {
    type Data<'src> = OwnedPcgNode<'tcx> where 'tcx: 'src;
}

pub(crate) trait FromData<'src, 'tcx, IData: InternalData<'tcx>>:
    InternalData<'tcx>
{
    fn lower(data: &'src IData::Data<'_>) -> Self::Data<'src>;
}

impl<'tcx, T: Clone + Eq + std::fmt::Debug> InternalData<'tcx> for Shallow<T> {
    type Data<'src> = T where 'tcx: 'src;
}

impl<'src, 'tcx, IData: InternalData<'tcx>> FromData<'src, 'tcx, IData> for Shallow<()> {
    fn lower(_data: &'src IData::Data<'_>) -> () {
        ()
    }
}

impl<'src, 'tcx: 'src> FromData<'src, 'tcx, Deep> for DeepRef {
    fn lower(data: &'src OwnedPcgNode<'tcx, Deep>) -> &'src OwnedPcgNode<'tcx, Deep> {
        data
    }
}
