//! Aggregate edges
use crate::{
    HasSettings,
    borrow_pcg::{
        borrow_pcg_edge::{BlockedNode, LocalNode},
        edge::kind::BorrowPcgEdgeType,
        edge_data::{
            EdgeData, LabelEdgeLifetimeProjections, LabelEdgePlaces, LabelNodePredicate,
            NodeReplacement, conditionally_label_places,
        },
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionResult, LabelNodeContext, LabelPlace,
            PlaceLabeller, SourceOrTarget,
        },
        region_projection::{
            LifetimeProjection, LifetimeProjectionLabel, LifetimeProjectionWithPlace,
            LocalLifetimeProjection, PcgLifetimeProjectionBase,
        },
    },
    pcg::{PcgNode, PcgNodeLike},
    utils::{
        DebugCtxt, HasBorrowCheckerCtxt, PcgPlace, Place,
        data_structures::HashSet,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        validity::HasValidityCheck,
    },
};

/// The lifetime projections of the parts of a value flowing into one lifetime
/// projection of the value, e.g. `{a|'a, b|'a} -> x|'a` for
/// `x = S { f: a, g: b }`. A single edge stands for all parts, so that the
/// value's projection is created and removed in one step.
///
/// Introduced in two cases:
/// 1. Assigning an aggregate (e.g. `x = Aggregate(a, b)`): the (labelled)
///    operands flow into the lifetime projections of `x` they outlive.
/// 2. Collapsing an owned place: the (labelled) lifetime projections of the
///    places it was expanded into flow into the place's projection.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct AggregateEdge<'tcx, P = Place<'tcx>> {
    sources: Vec<LifetimeProjection<'tcx, PcgLifetimeProjectionBase<'tcx, P>>>,
    /// For each source, the index of the operand of the assigned aggregate
    /// it is a lifetime projection of (case 1), or `None` for a part of a
    /// collapsed place (case 2), whose place says which part it is.
    operand_indices: Vec<Option<usize>>,
    pub(crate) target: LocalLifetimeProjection<'tcx, P>,
}

impl<'tcx, P: Copy> AggregateEdge<'tcx, P> {
    pub(crate) fn new(
        sources: Vec<(
            LifetimeProjection<'tcx, PcgLifetimeProjectionBase<'tcx, P>>,
            Option<usize>,
        )>,
        target: LocalLifetimeProjection<'tcx, P>,
    ) -> Self {
        let (sources, operand_indices) = sources.into_iter().unzip();
        Self {
            sources,
            operand_indices,
            target,
        }
    }

    /// The lifetime projections of the parts.
    pub fn sources(&self) -> &[LifetimeProjection<'tcx, PcgLifetimeProjectionBase<'tcx, P>>] {
        &self.sources
    }

    /// The lifetime projections of the parts, each with the index of the
    /// aggregate's operand it is a lifetime projection of, if the edge is for
    /// an assigned aggregate.
    pub fn sources_with_operand_indices(
        &self,
    ) -> impl Iterator<
        Item = (
            LifetimeProjection<'tcx, PcgLifetimeProjectionBase<'tcx, P>>,
            Option<usize>,
        ),
    > + '_ {
        self.sources
            .iter()
            .copied()
            .zip(self.operand_indices.iter().copied())
    }

    /// The lifetime projection of the value.
    pub fn target(&self) -> LocalLifetimeProjection<'tcx, P> {
        self.target
    }
}

const EDGE_TYPE: BorrowPcgEdgeType = BorrowPcgEdgeType::Aggregate;

impl<'tcx, Ctxt: Copy + DebugCtxt, P: PcgPlace<'tcx, Ctxt>> LabelEdgePlaces<'tcx, Ctxt, P>
    for AggregateEdge<'tcx, P>
where
    LifetimeProjectionWithPlace<'tcx, P>: LabelPlace<'tcx, Ctxt, P>,
    LocalLifetimeProjection<'tcx, P>: LabelPlace<'tcx, Ctxt, P>,
{
    fn label_blocked_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>> {
        conditionally_label_places(
            self.sources.iter_mut(),
            predicate,
            labeller,
            LabelNodeContext::new(SourceOrTarget::Source, EDGE_TYPE),
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
            vec![&mut self.target],
            predicate,
            labeller,
            LabelNodeContext::new(SourceOrTarget::Target, EDGE_TYPE),
            ctxt,
        )
    }
}

impl<'a, 'tcx, Ctxt: Copy + DebugCtxt + HasSettings<'a>, P: PcgPlace<'tcx, Ctxt>>
    LabelEdgeLifetimeProjections<'tcx, Ctxt, P> for AggregateEdge<'tcx, P>
where
    Self: DisplayWithCtxt<Ctxt> + HasValidityCheck<Ctxt>,
    LifetimeProjectionWithPlace<'tcx, P>: LabelLifetimeProjection<'tcx>,
    LocalLifetimeProjection<'tcx, P>: LabelLifetimeProjection<'tcx>,
{
    fn label_lifetime_projections(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: Ctxt,
    ) -> LabelLifetimeProjectionResult {
        let source_context = LabelNodeContext::new(SourceOrTarget::Source, EDGE_TYPE);
        let matching_sources = self
            .sources
            .iter()
            .map(|source| {
                predicate.applies_to(PcgNode::LifetimeProjection(*source), source_context)
            })
            .collect::<Vec<_>>();
        let target_matches = predicate.applies_to(
            PcgNode::LifetimeProjection(self.target.rebase()),
            LabelNodeContext::new(SourceOrTarget::Target, EDGE_TYPE),
        );
        if target_matches && matching_sources.iter().any(|&matches| matches) {
            return LabelLifetimeProjectionResult::ShouldCollapse;
        }
        let mut changed = LabelLifetimeProjectionResult::Unchanged;
        for (source, matches) in self.sources.iter_mut().zip(matching_sources) {
            if matches {
                changed |= source.label_lifetime_projection(label);
            }
        }
        if target_matches {
            changed |= self.target.label_lifetime_projection(label);
        }
        self.assert_validity(ctxt);
        changed
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for AggregateEdge<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        let sources = self
            .sources
            .iter()
            .map(|source| DisplayWithCtxt::<_>::display_string(source, ctxt))
            .collect::<Vec<_>>()
            .join(", ");
        DisplayOutput::Text(
            format!(
                "aggregate {{{}}} -> {}",
                sources,
                self.target.display_string(ctxt)
            )
            .into(),
        )
    }
}

impl<'tcx, Ctxt: Copy, P: PartialEq + Copy> EdgeData<'tcx, Ctxt, P> for AggregateEdge<'tcx, P>
where
    LifetimeProjection<'tcx, PcgLifetimeProjectionBase<'tcx, P>>: PcgNodeLike<'tcx, Ctxt, P>,
    LocalLifetimeProjection<'tcx, P>: PcgNodeLike<'tcx, Ctxt, P>,
{
    fn blocks_node<'slf>(&self, node: BlockedNode<'tcx, P>, ctxt: Ctxt) -> bool {
        self.sources
            .iter()
            .any(|source| source.to_pcg_node(ctxt) == node)
    }

    fn blocked_nodes<'slf>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Box<dyn Iterator<Item = BlockedNode<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        let nodes = self
            .sources
            .iter()
            .map(|source| source.to_pcg_node(ctxt))
            .collect::<Vec<_>>();
        Box::new(nodes.into_iter())
    }

    fn blocked_by_nodes<'slf>(
        &'slf self,
        _ctxt: Ctxt,
    ) -> Box<dyn Iterator<Item = LocalNode<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(std::iter::once(PcgNode::LifetimeProjection(self.target)))
    }
}

impl<'tcx, Ctxt: Copy + DebugCtxt, P: PcgPlace<'tcx, Ctxt>> HasValidityCheck<Ctxt>
    for AggregateEdge<'tcx, P>
where
    Self: DisplayWithCtxt<Ctxt>,
    LifetimeProjectionWithPlace<'tcx, P>: HasValidityCheck<Ctxt>,
    LocalLifetimeProjection<'tcx, P>: HasValidityCheck<Ctxt>,
{
    fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
        if self.sources.is_empty() {
            return Err(format!(
                "AggregateEdge without sources: {}",
                self.display_string(ctxt)
            ));
        }
        for source in &self.sources {
            source.check_validity(ctxt)?;
            if *source == self.target.rebase() {
                return Err(format!(
                    "AggregateEdge: a source is the target: {}",
                    self.display_string(ctxt)
                ));
            }
        }
        self.target.check_validity(ctxt)
    }
}
