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
        region_projection::{LifetimeProjectionLabel, LocalLifetimeProjection},
    },
    pcg::{LocalNodeLike, PcgNode, PcgNodeLike},
    rustc_interface::middle::mir,
    utils::{
        CompilerCtxt, DebugCtxt, HasBorrowCheckerCtxt, PcgPlace, Place, PlaceProjectable, SnapshotLocation, data_structures::HashSet, display::{DisplayOutput, DisplayWithCtxt, OutputMode}, maybe_old::MaybeLabelledPlace, validity::HasValidityCheck
    },
};

/// A PCG Hyperedge from the a reference-typed place, and a lifetime projection
/// to the dereferenced place.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct DerefEdge<'tcx, P = Place<'tcx>> {
    pub(crate) blocked_place: MaybeLabelledPlace<'tcx, P>,
    pub(crate) deref_place: MaybeLabelledPlace<'tcx, P>,
    /// The lifetime projection that is blocked in this edge. In general, this
    /// will not be labelled if `blocked_place` is a shared reference, and
    /// labelled with the MIR location of the dereference if `blocked_place` is
    /// a mutable reference.
    pub(crate) blocked_lifetime_projection: LocalLifetimeProjection<'tcx, P>,
}

impl<'tcx> DerefEdge<'tcx> {
    #[must_use]
    pub fn blocked_place(self) -> MaybeLabelledPlace<'tcx> {
        self.blocked_place
    }
    #[must_use]
    pub fn deref_place(self) -> MaybeLabelledPlace<'tcx> {
        self.deref_place
    }

    pub(crate) fn new<'a>(
        place: Place<'tcx>,
        blocked_lifetime_projection_label: Option<SnapshotLocation>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Self
    where
        'tcx: 'a,
    {
        let blocked_lifetime_projection = place
            .base_lifetime_projection(ctxt)
            .unwrap()
            .with_label(
                blocked_lifetime_projection_label.map(std::convert::Into::into),
                ctxt,
            )
            .into();
        let blocked_place_label: Option<SnapshotLocation> = None;
        DerefEdge {
            blocked_place: MaybeLabelledPlace::new(place, blocked_place_label),
            deref_place: place.project_deref(ctxt).unwrap().into(),
            blocked_lifetime_projection,
        }
    }
}

impl<'a, 'tcx> HasValidityCheck<CompilerCtxt<'a, 'tcx>> for DerefEdge<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> Result<(), String> {
        self.blocked_place.check_validity(ctxt)?;
        self.deref_place.check_validity(ctxt)?;
        self.blocked_lifetime_projection.check_validity(ctxt)?;
        if self.deref_place.last_projection().unwrap().1 != mir::PlaceElem::Deref {
            return Err("Deref edge deref place must end with a deref projection".to_owned());
        }
        Ok(())
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt> for DerefEdge<'tcx> {
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
    for DerefEdge<'tcx, P>
{
    fn label_lifetime_projections(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: Ctxt,
    ) -> LabelLifetimeProjectionResult {
        let node_context = LabelNodeContext::new(SourceOrTarget::Source, BorrowPcgEdgeType::Deref);
        if predicate.applies_to(
            PcgNode::LifetimeProjection(self.blocked_lifetime_projection.rebase()),
            node_context,
        ) {
            self.blocked_lifetime_projection =
                self.blocked_lifetime_projection.with_label(label, ctxt);
            LabelLifetimeProjectionResult::Changed
        } else {
            LabelLifetimeProjectionResult::Unchanged
        }
    }
}

impl<'tcx, Ctxt: DebugCtxt + Copy, P: PcgPlace<'tcx, Ctxt>> LabelEdgePlaces<'tcx, Ctxt, P>
    for DerefEdge<'tcx, P>
where
    MaybeLabelledPlace<'tcx, P>: LabelPlace<'tcx, Ctxt, P>,
{
    fn label_blocked_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>> {
        let blocked_places: Vec<&mut MaybeLabelledPlace<'tcx, P>> = vec![
            &mut self.blocked_place,
            &mut self.blocked_lifetime_projection.base,
        ];
        conditionally_label_places(
            blocked_places,
            predicate,
            labeller,
            LabelNodeContext::new(SourceOrTarget::Source, BorrowPcgEdgeType::Deref),
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
            LabelNodeContext::new(SourceOrTarget::Target, BorrowPcgEdgeType::Deref),
            ctxt,
        )
    }
}

impl<'tcx, Ctxt: Copy, P: PcgPlace<'tcx, Ctxt>> EdgeData<'tcx, Ctxt, P> for DerefEdge<'tcx, P> {
    fn blocked_nodes<'slf>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Box<dyn std::iter::Iterator<Item = BlockedNode<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(
            vec![
                self.blocked_place.to_pcg_node(ctxt),
                self.blocked_lifetime_projection.to_pcg_node(ctxt),
            ]
            .into_iter(),
        )
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
