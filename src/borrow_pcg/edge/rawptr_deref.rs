use crate::{
    HasCompilerCtxt,
    borrow_pcg::{
        borrow_pcg_edge::{BlockedNode, LocalNode},
        edge::kind::BorrowPcgEdgeType,
        edge_data::{
            EdgeData, LabelEdgeLifetimeProjections, LabelEdgePlaces, LabelNodePredicate,
            NodeReplacement, conditionally_label_places,
        },
        has_pcs_elem::{
            LabelLifetimeProjectionResult, LabelNodeContext, LabelPlace, PlaceLabeller,
            SourceOrTarget,
        },
    },
    pcg::{LocalNodeLike, PcgNodeLike},
    utils::{
        DebugCtxt, HasBorrowCheckerCtxt, PcgPlace, Place, SnapshotLocation,
        data_structures::HashSet,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        maybe_old::MaybeLabelledPlace,
        validity::HasValidityCheck,
    },
};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct RawPtrDerefEdge<'tcx, P = Place<'tcx>> {
    pub(crate) blocked_place: MaybeLabelledPlace<'tcx, P>,
    pub(crate) deref_place: MaybeLabelledPlace<'tcx, P>,
}

impl<'tcx> RawPtrDerefEdge<'tcx> {
    #[must_use]
    pub fn blocked_place(self) -> MaybeLabelledPlace<'tcx> {
        self.blocked_place
    }
    #[must_use]
    pub fn deref_place(self) -> MaybeLabelledPlace<'tcx> {
        self.deref_place
    }

    pub(crate) fn new<'a>(place: Place<'tcx>, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> Self
    where
        'tcx: 'a,
    {
        let blocked_place_label: Option<SnapshotLocation> = None;
        RawPtrDerefEdge {
            blocked_place: MaybeLabelledPlace::new(place, blocked_place_label),
            deref_place: place.project_deref(ctxt).into(),
        }
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx> + DebugCtxt> HasValidityCheck<Ctxt>
    for RawPtrDerefEdge<'tcx>
{
    fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
        self.blocked_place.check_validity(ctxt)?;
        self.deref_place.check_validity(ctxt)?;
        Ok(())
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for RawPtrDerefEdge<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(
            format!(
                "{{{}}} -> {{{}}}",
                self.blocked_place.display_output(ctxt, mode).into_text(),
                self.deref_place.display_output(ctxt, mode).into_text()
            )
            .into(),
        )
    }
}

impl<'tcx, Ctxt, P: PcgPlace<'tcx, Ctxt>> LabelEdgeLifetimeProjections<'tcx, Ctxt, P>
    for RawPtrDerefEdge<'tcx>
{
    fn label_lifetime_projections(
        &mut self,
        _predicate: &crate::borrow_pcg::edge_data::LabelNodePredicate<'tcx, P>,
        _label: Option<crate::borrow_pcg::region_projection::LifetimeProjectionLabel>,
        _ctxt: Ctxt,
    ) -> LabelLifetimeProjectionResult {
        LabelLifetimeProjectionResult::Unchanged
    }
}

impl<'tcx, Ctxt: DebugCtxt, P: PcgPlace<'tcx, Ctxt>> LabelEdgePlaces<'tcx, Ctxt, P>
    for RawPtrDerefEdge<'tcx, P>
where
    MaybeLabelledPlace<'tcx, P>: LabelPlace<'tcx, Ctxt, P>,
{
    fn label_blocked_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>> {
        let blocked_places: Vec<&mut MaybeLabelledPlace<'tcx, P>> = vec![&mut self.blocked_place];
        conditionally_label_places(
            blocked_places,
            predicate,
            labeller,
            LabelNodeContext::new(SourceOrTarget::Source, BorrowPcgEdgeType::RawPtrDeref),
            ctxt,
        )
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>> {
        conditionally_label_places(
            vec![&mut self.deref_place],
            predicate,
            labeller,
            LabelNodeContext::new(SourceOrTarget::Target, BorrowPcgEdgeType::RawPtrDeref),
            ctxt,
        )
    }
}

impl<'tcx, Ctxt: Copy, P: PcgPlace<'tcx, Ctxt>> EdgeData<'tcx, Ctxt, P>
    for RawPtrDerefEdge<'tcx, P>
{
    fn blocked_nodes<'slf>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Box<dyn std::iter::Iterator<Item = BlockedNode<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(vec![self.blocked_place.to_pcg_node(ctxt)].into_iter())
    }

    fn blocked_by_nodes<'slf>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(vec![self.deref_place.to_local_node(ctxt)].into_iter())
    }
}
