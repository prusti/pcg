use crate::{
    borrow_pcg::{borrow_pcg_edge::LocalNode, region_projection::{HasRegions, HasTy}}, pcg::{LocalNodeLike, PcgNode, PcgNodeLike, PcgNodeWithPlace}, utils::{PcgNodeComponent, PlaceProjectable, PrefixRelation, maybe_old::MaybeLabelledPlace}
};

pub trait PcgPlace<'tcx, Ctxt: Copy> = PlaceProjectable<'tcx, Ctxt>
    + PcgNodeComponent
    + HasRegions<'tcx, Ctxt>
    + HasTy<'tcx, Ctxt>
    + PrefixRelation
    + Ord
    + 'tcx;

impl<'tcx, Ctxt, P: PcgPlace<'tcx, Ctxt>> LocalNodeLike<'tcx, Ctxt, P> for P {
    fn to_local_node(self, _ctxt: Ctxt) -> LocalNode<'tcx, P> {
        LocalNode::Place(self.into())
    }
}

impl<'tcx, Ctxt, P: PcgPlace<'tcx, Ctxt>> LocalNodeLike<'tcx, Ctxt, P>
    for MaybeLabelledPlace<'tcx, P>
{
    fn to_local_node(self, _ctxt: Ctxt) -> LocalNode<'tcx, P> {
        LocalNode::Place(self)
    }
}

impl<'tcx, Ctxt, P: PcgPlace<'tcx, Ctxt>> PcgNodeLike<'tcx, Ctxt, P> for P {
    fn to_pcg_node(self, _ctxt: Ctxt) -> PcgNodeWithPlace<'tcx, P> {
        PcgNode::Place(self.into())
    }
}
