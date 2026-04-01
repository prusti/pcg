use crate::{
    error::{PcgError},
    pcg::{
        obtain::ObtainType, triple::{PlaceCondition, Triple}
    },
    utils::{DataflowCtxt},
};

use super::PcgVisitor;

impl<'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PcgVisitor<'_, 'a, 'tcx, Ctxt> {
    #[tracing::instrument(skip(self))]
    pub(crate) fn require_triple(&mut self, triple: Triple<'tcx>) -> Result<(), PcgError<'tcx>> {
        match triple.pre() {
            PlaceCondition::ExpandTwoPhase(place) => {
                /*if place.contains_unsafe_deref(self.ctxt) {
                    let node = PcgNode::from(place/*.target_place().unwrap()*/);
                    let edges = self.pcg.borrow_pcg().edges_blocking(node, self.tw.ctxt);
                    let raw_ptr_edge = edges.into_iter().filter_map(|e| match e.kind {
                        crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind::RawPtrAlias(raw_ptr_edge) => Some(raw_ptr_edge),
                        _ => None
                    }).collect::<Vec<_>>();
                    assert!(raw_ptr_edge.len() == 1);
                    let target_place = raw_ptr_edge[0].aliased_place.place();
                    self.place_obtainer().obtain(target_place, ObtainType::TwoPhaseExpand)?;
                } else {*/
                    self.place_obtainer()
                        .obtain(place, ObtainType::TwoPhaseExpand)?;
                //}
            }
            PlaceCondition::Capability(place, capability) => {
                // if place.contains_unsafe_deref(self.ctxt) {
                    // println!("{:?}", place.ty(self.ctxt).ty);
                    // let node = PcgNode::from(place/*.target_place().unwrap()*/);
                    // println!("{:?}", node);
                    // let edges = self.pcg.borrow_pcg().edges_blocking(node, self.tw.ctxt);
                    // println!("{:?}", edges);
                    // let raw_ptr_edge = edges.into_iter().filter_map(|e| match e.kind {
                    //     crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind::RawPtrAlias(raw_ptr_edge) => Some(raw_ptr_edge),
                    //     _ => None
                    // }).collect::<Vec<_>>();
                    // assert!(raw_ptr_edge.len() == 1);
                    // let target_place = raw_ptr_edge[0].aliased_place.place();
                    // self.place_obtainer().obtain(target_place, ObtainType::Capability(capability))?;
                // } else {
                    self.place_obtainer()
                        .obtain(place, ObtainType::Capability(capability))?;
                // }
            }
            PlaceCondition::AllocateOrDeallocate(local) => {
                if self.pcg.owned[local].is_unallocated() {
                    // Could happen if there is a storagedead for an already conditionally dead local
                    return Ok(());
                }
                self.place_obtainer()
                    .obtain(local.into(), ObtainType::ForStorageDead)?;
            }
            PlaceCondition::Unalloc(_) | PlaceCondition::Return => {}
            PlaceCondition::RemoveCapability(_) => unreachable!(),
        }
        Ok(())
    }

    #[tracing::instrument(skip(self, triple))]
    pub(crate) fn ensure_triple(&mut self, triple: Triple<'tcx>) -> Result<(), PcgError<'tcx>> {
        self.pcg.ensure_triple(triple, self.ctxt);
        Ok(())
    }
}
