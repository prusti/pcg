use std::collections::HashSet;

use crate::{
    borrow_pcg::{
        self, borrow_pcg_edge,
        edge::kind::BorrowPcgEdgeType,
        edge_data::{
            EdgeData, LabelEdgeLifetimeProjections, LabelEdgePlaces, conditionally_label_places,
        },
        has_pcs_elem::{
            LabelLifetimeProjectionResult, LabelNodeContext, LabelPlace, SourceOrTarget,
        },
    },
    utils::{
        CompilerCtxt, DebugCtxt, HasBorrowCheckerCtxt, PcgPlace, Place, data_structures,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        maybe_old::MaybeLabelledPlace,
        validity::HasValidityCheck,
    },
};
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct DelegationEdge<'tcx, P = Place<'tcx>> {
    pub(crate) rawptr_place: MaybeLabelledPlace<'tcx, P>,
    pub(crate) aliased_place: MaybeLabelledPlace<'tcx, P>,
}

impl<'tcx, Ctxt: Copy, P: PcgPlace<'tcx, Ctxt>> EdgeData<'tcx, Ctxt, P>
    for DelegationEdge<'tcx, P>
{
    fn blocked_nodes<'slf>(
        &'slf self,
        _ctxt: Ctxt,
    ) -> Box<dyn std::iter::Iterator<Item = borrow_pcg_edge::BlockedNode<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(vec![self.aliased_place.into()].into_iter())
    }

    fn blocked_by_nodes<'slf>(
        &'slf self,
        _ctxt: Ctxt,
    ) -> Box<dyn std::iter::Iterator<Item = borrow_pcg_edge::LocalNode<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(vec![self.rawptr_place.into()].into_iter())
    }
}

impl<'a, 'tcx> HasValidityCheck<CompilerCtxt<'a, 'tcx>> for DelegationEdge<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> Result<(), String> {
        self.aliased_place.check_validity(ctxt)?;
        self.rawptr_place.check_validity(ctxt)?;
        if self.rawptr_place.place().ty(ctxt).ty.is_raw_ptr() {
            Err("RawPtr edge must originate in a rawptr".to_owned())
        } else {
            Ok(())
        }
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for DelegationEdge<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(
            format!(
                "{{{}}} -=-> {{{}}}",
                self.aliased_place.display_output(ctxt, mode).into_text(),
                self.rawptr_place.display_output(ctxt, mode).into_text()
            )
            .into(),
        )
    }
}

impl<'tcx, Ctxt, P: PcgPlace<'tcx, Ctxt>> LabelEdgeLifetimeProjections<'tcx, Ctxt, P>
    for DelegationEdge<'tcx>
{
    fn label_lifetime_projections(
        &mut self,
        _predicate: &borrow_pcg::edge_data::LabelNodePredicate<'tcx, P>,
        _label: Option<borrow_pcg::region_projection::LifetimeProjectionLabel>,
        _ctxt: Ctxt,
    ) -> LabelLifetimeProjectionResult {
        LabelLifetimeProjectionResult::Unchanged
    }
}

impl<'tcx, Ctxt: DebugCtxt + Copy, P: PcgPlace<'tcx, Ctxt>> LabelEdgePlaces<'tcx, Ctxt, P>
    for DelegationEdge<'tcx, P>
where
    MaybeLabelledPlace<'tcx, P>: LabelPlace<'tcx, Ctxt, P>,
{
    fn label_blocked_places(
        &mut self,
        predicate: &borrow_pcg::edge_data::LabelNodePredicate<'tcx, P>,
        labeller: &impl borrow_pcg::has_pcs_elem::PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> data_structures::HashSet<borrow_pcg::edge_data::NodeReplacement<'tcx, P>> {
        conditionally_label_places(
            vec![&mut self.aliased_place],
            predicate,
            labeller,
            LabelNodeContext::new(SourceOrTarget::Target, BorrowPcgEdgeType::Delegation),
            ctxt,
        )
    }

    fn label_blocked_by_places(
        &mut self,
        _predicate: &borrow_pcg::edge_data::LabelNodePredicate<'tcx, P>,
        _labeller: &impl borrow_pcg::has_pcs_elem::PlaceLabeller<'tcx, Ctxt, P>,
        _ctxt: Ctxt,
    ) -> data_structures::HashSet<borrow_pcg::edge_data::NodeReplacement<'tcx, P>> {
        HashSet::default()
    }
}
