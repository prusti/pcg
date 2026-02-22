use std::marker::PhantomData;

use crate::owned_pcg::{OwnedExpansion, OwnedPcgInternalNode, node::OwnedPcgNode};

pub trait InternalData<'tcx>: Sized {
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
    fn lower(data: &'src IData::Data) -> Self::Data;
}

impl<'tcx, T: Clone + Eq + std::fmt::Debug> InternalData<'tcx> for Shallow<T> {
    type Data = T;
}

impl<'src, 'tcx, IData: InternalData<'tcx>> FromData<'src, 'tcx, IData> for Shallow<()> {
    fn lower(_data: &'src IData::Data) -> () {
        ()
    }
}

impl<'src, 'tcx: 'src> FromData<'src, 'tcx, Deep> for DeepRef<'src> {
    fn lower(data: &'src OwnedPcgNode<'tcx, Deep>) -> &'src OwnedPcgNode<'tcx, Deep> {
        data
    }
}
