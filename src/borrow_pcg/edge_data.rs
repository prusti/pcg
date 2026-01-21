use crate::{
    borrow_pcg::{
        edge::kind::BorrowPcgEdgeType,
        has_pcs_elem::{LabelNodeContext, PlaceLabeller, SourceOrTarget},
        region_projection::{LifetimeProjectionLabel, RegionIdx},
    },
    pcg::{LabelPlaceConditionally, MaybeHasLocation, PcgNode, PcgNodeType},
    utils::{
        CompilerCtxt, HasBorrowCheckerCtxt, HasPlace, Place, SnapshotLocation,
        data_structures::HashSet,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
    },
};

use super::borrow_pcg_edge::{BlockedNode, LocalNode};

/// A trait for data that represents a hyperedge in the Borrow PCG.
pub trait EdgeData<'tcx> {
    /// For an edge A -> B, this returns the set of nodes A. In general, the capabilities
    /// of nodes B are obtained from these nodes.
    fn blocked_nodes<'slf, BC: Copy>(
        &'slf self,
        ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = PcgNode<'tcx>> + 'slf>
    where
        'tcx: 'slf;

    /// For an edge A -> B, this returns the set of nodes B. In general, these nodes
    /// obtain their capabilities from the nodes A.
    fn blocked_by_nodes<'slf, 'mir: 'slf, BC: Copy + 'slf>(
        &'slf self,
        ctxt: CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx>> + 'slf>
    where
        'tcx: 'mir;

    fn blocks_node(&self, node: BlockedNode<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.blocked_nodes(ctxt).any(|n| n == node)
    }

    fn is_blocked_by(&self, node: LocalNode<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.blocked_by_nodes(ctxt).any(|n| n == node)
    }

    fn nodes<'slf, 'mir: 'slf, BC: Copy + 'slf>(
        &'slf self,
        ctxt: CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = PcgNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(
            self.blocked_nodes(ctxt)
                .chain(self.blocked_by_nodes(ctxt).map(|n| n.into())),
        )
    }

    fn references_place(&self, place: Place<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.nodes(ctxt).any(|n| match n {
            PcgNode::Place(p) => p.as_current_place() == Some(place),
            PcgNode::LifetimeProjection(rp) => rp.base.as_current_place() == Some(place),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LabelNodePredicate<'tcx, P = Place<'tcx>> {
    LifetimeProjectionLabelEquals(Option<LifetimeProjectionLabel>),
    PlaceLabelEquals(Option<SnapshotLocation>),
    ProjectionRegionIdxEquals(RegionIdx),
    Equals(PcgNode<'tcx>),
    /// The place associated with the node is exactly this place.
    PlaceEquals(P),
    /// The place associated with the node is a postfix of this place.
    PlaceIsPostfixOf(P),
    NodeType(PcgNodeType),
    And(Vec<Self>),
    Or(Vec<Self>),
    Not(Box<Self>),
    EdgeType(BorrowPcgEdgeType),
    InSourceNodes,
    InTargetNodes,
}

impl<'tcx, P: Copy> LabelNodePredicate<'tcx, P> {
    /// Creates a predicate that matches all future lifetime projections whose base
    /// is a postfix of the given place (and the base is current, not labelled).
    pub(crate) fn all_future_postfixes(place: P) -> Self {
        Self::And(vec![
            Self::LifetimeProjectionLabelEquals(Some(LifetimeProjectionLabel::Future)),
            Self::PlaceLabelEquals(None),
            Self::PlaceIsPostfixOf(place),
        ])
    }

    pub(crate) fn not(self) -> Self {
        Self::Not(Box::new(self))
    }
}

impl<'tcx> LabelNodePredicate<'tcx> {
    /// Creates a predicate that matches all non-future lifetime projections with
    /// the given base place and region index.
    pub(crate) fn all_non_future(
        place: crate::utils::place::maybe_old::MaybeLabelledPlace<'tcx>,
        region_idx: RegionIdx,
    ) -> Self {
        Self::And(vec![
            Self::PlaceEquals(place.place()),
            Self::PlaceLabelEquals(place.location()),
            Self::ProjectionRegionIdxEquals(region_idx),
            Self::LifetimeProjectionLabelEquals(Some(LifetimeProjectionLabel::Future)).not(),
        ])
    }

    /// Creates a predicate that matches lifetime projections that are postfixes
    /// of the given projection (same region, same label, and base is a postfix).
    pub(crate) fn postfix_lifetime_projection(
        projection: crate::borrow_pcg::region_projection::LifetimeProjection<
            'tcx,
            crate::utils::place::maybe_old::MaybeLabelledPlace<'tcx>,
        >,
    ) -> Self {
        Self::And(vec![
            Self::PlaceIsPostfixOf(projection.base.place()),
            Self::PlaceLabelEquals(projection.base.location()),
            Self::ProjectionRegionIdxEquals(projection.region_idx),
            Self::LifetimeProjectionLabelEquals(projection.label()),
        ])
    }

    /// Creates a predicate that matches exactly the given lifetime projection.
    pub(crate) fn equals_lifetime_projection(
        projection: crate::borrow_pcg::region_projection::LifetimeProjection<
            'tcx,
            crate::utils::place::maybe_old::MaybeLabelledPlace<'tcx>,
        >,
    ) -> Self {
        Self::Equals(PcgNode::LifetimeProjection(projection.rebase()))
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for LabelNodePredicate<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        match self {
            LabelNodePredicate::PlaceIsPostfixOf(place) => DisplayOutput::Seq(vec![
                "postfixes of ".into(),
                place.display_output(ctxt, mode),
            ]),
            LabelNodePredicate::PlaceEquals(place) => {
                DisplayOutput::Seq(vec!["exact ".into(), place.display_output(ctxt, mode)])
            }
            LabelNodePredicate::NodeType(pcg_node_type) => {
                format!("node_type({pcg_node_type:?})").into()
            }
            LabelNodePredicate::And(predicates) => DisplayOutput::Seq(vec![
                "(".into(),
                DisplayOutput::join(
                    predicates.iter().map(|p| p.display_output(ctxt, mode)),
                    " && ".into(),
                ),
                ")".into(),
            ]),
            LabelNodePredicate::Or(predicates) => DisplayOutput::Seq(vec![
                "(".into(),
                DisplayOutput::join(
                    predicates.iter().map(|p| p.display_output(ctxt, mode)),
                    " || ".into(),
                ),
                ")".into(),
            ]),
            LabelNodePredicate::Not(predicate) => {
                DisplayOutput::Seq(vec!["!".into(), predicate.display_output(ctxt, mode)])
            }
            LabelNodePredicate::EdgeType(edge_type) => format!("edge_type({edge_type:?})").into(),
            LabelNodePredicate::InSourceNodes => "in_source_nodes".into(),
            LabelNodePredicate::InTargetNodes => "in_target_nodes".into(),
            LabelNodePredicate::LifetimeProjectionLabelEquals(label) => {
                format!("rp_label({label:?})").into()
            }
            LabelNodePredicate::PlaceLabelEquals(location) => {
                format!("place_label({location:?})").into()
            }
            LabelNodePredicate::ProjectionRegionIdxEquals(region_idx) => {
                format!("region_idx({region_idx:?})").into()
            }
            LabelNodePredicate::Equals(pcg_node) => pcg_node.display_output(ctxt, mode),
        }
    }
}

impl<'tcx> LabelNodePredicate<'tcx> {
    pub(crate) fn applies_to(
        &self,
        candidate: PcgNode<'tcx>,
        label_context: LabelNodeContext,
    ) -> bool {
        let related_maybe_labelled_place = candidate.related_maybe_labelled_place();
        let related_place = related_maybe_labelled_place.map(|p| p.place());
        match self {
            LabelNodePredicate::PlaceEquals(place) => related_place.is_some_and(|p| p == *place),
            LabelNodePredicate::PlaceIsPostfixOf(place) => {
                related_place.is_some_and(|p| place.is_prefix_of(p))
            }
            LabelNodePredicate::NodeType(pcg_node_type) => match candidate {
                PcgNode::Place(_) => *pcg_node_type == PcgNodeType::Place,
                PcgNode::LifetimeProjection(_) => *pcg_node_type == PcgNodeType::LifetimeProjection,
            },
            LabelNodePredicate::And(predicates) => predicates
                .iter()
                .all(|p| p.applies_to(candidate, label_context)),
            LabelNodePredicate::Or(predicates) => predicates
                .iter()
                .any(|p| p.applies_to(candidate, label_context)),
            LabelNodePredicate::Not(predicate) => !predicate.applies_to(candidate, label_context),
            LabelNodePredicate::EdgeType(edge_type) => label_context.edge_type() == *edge_type,
            LabelNodePredicate::InSourceNodes => {
                label_context.source_or_target() == SourceOrTarget::Source
            }
            LabelNodePredicate::InTargetNodes => {
                label_context.source_or_target() == SourceOrTarget::Target
            }
            LabelNodePredicate::LifetimeProjectionLabelEquals(label) => {
                if let PcgNode::LifetimeProjection(rp) = candidate {
                    rp.label == *label
                } else {
                    false
                }
            }
            LabelNodePredicate::PlaceLabelEquals(location) => {
                related_maybe_labelled_place.is_some_and(|p| p.location() == *location)
            }
            LabelNodePredicate::ProjectionRegionIdxEquals(region_idx) => match candidate {
                PcgNode::Place(_) => false,
                PcgNode::LifetimeProjection(rp) => rp.region_idx == *region_idx,
            },
            LabelNodePredicate::Equals(node) => candidate == *node,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NodeReplacement<'tcx> {
    pub(crate) from: PcgNode<'tcx>,
    pub(crate) to: PcgNode<'tcx>,
}

impl<'tcx> NodeReplacement<'tcx> {
    pub(crate) fn new(from: PcgNode<'tcx>, to: PcgNode<'tcx>) -> Self {
        Self { from, to }
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for NodeReplacement<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Seq(vec![
            self.from.display_output(ctxt, mode),
            " → ".into(),
            self.to.display_output(ctxt, mode),
        ])
    }
}

pub(crate) fn display_node_replacements<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
    replacements: &HashSet<NodeReplacement<'tcx>>,
    ctxt: Ctxt,
    mode: OutputMode,
) -> DisplayOutput {
    if replacements.is_empty() {
        return DisplayOutput::EMPTY;
    }
    let items: Vec<DisplayOutput> = replacements
        .iter()
        .map(|r| r.display_output(ctxt, mode))
        .collect();
    DisplayOutput::Seq(vec![
        "Labelled nodes: [".into(),
        DisplayOutput::join(items, ", ".into()),
        "]".into(),
    ])
}

pub(crate) fn conditionally_label_places<'pcg, 'tcx, Node: LabelPlaceConditionally<'tcx> + 'pcg>(
    nodes: impl IntoIterator<Item = &'pcg mut Node>,
    predicate: &LabelNodePredicate<'tcx>,
    labeller: &impl PlaceLabeller<'tcx>,
    label_context: LabelNodeContext,
    ctxt: CompilerCtxt<'_, 'tcx>,
) -> HashSet<NodeReplacement<'tcx>> {
    let mut result = HashSet::default();
    for node in nodes.into_iter() {
        node.label_place_conditionally(&mut result, predicate, labeller, label_context, ctxt);
    }
    result
}
pub trait LabelEdgePlaces<'tcx, P = Place<'tcx>> {
    fn label_blocked_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> HashSet<NodeReplacement<'tcx>>;

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> HashSet<NodeReplacement<'tcx>>;
}

use super::has_pcs_elem::LabelLifetimeProjectionResult;

/// Trait for labeling lifetime projections on edges.
/// Checks the predicate and then applies the label operation if it matches.
/// Analogous to `LabelEdgePlaces` for places.
pub trait LabelEdgeLifetimeProjections<'tcx, P = Place<'tcx>> {
    fn label_lifetime_projections(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> LabelLifetimeProjectionResult;
}

macro_rules! edgedata_enum {
    (
        $enum_name:ident < $tcx:lifetime >,
        $( $variant_name:ident($inner_type:ty) ),+ $(,)?
    ) => {
        impl<$tcx> $crate::borrow_pcg::edge_data::EdgeData<$tcx> for $enum_name<$tcx> {
            fn blocked_nodes<'slf, BC: Copy>(
                &'slf self,
                ctxt: CompilerCtxt<'_, $tcx, BC>,
            ) -> Box<dyn std::iter::Iterator<Item = PcgNode<'tcx>> + 'slf>
            where
                'tcx: 'slf,
            {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.blocked_nodes(ctxt),
                    )+
                }
            }

            fn blocked_by_nodes<'slf, 'mir: 'slf, BC: Copy + 'slf>(
                &'slf self,
                ctxt: CompilerCtxt<'mir, $tcx, BC>,
            ) -> Box<dyn std::iter::Iterator<Item = $crate::borrow_pcg::borrow_pcg_edge::LocalNode<'tcx>> + 'slf>
            where
                'tcx: 'mir,
            {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.blocked_by_nodes(ctxt),
                    )+
                }
            }

            fn blocks_node<'slf>(
                &self,
                node: BlockedNode<'tcx>,
                ctxt: CompilerCtxt<'_, $tcx>,
            ) -> bool {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.blocks_node(node, ctxt),
                    )+
                }
            }

            fn is_blocked_by<'slf>(
                &self,
                node: LocalNode<'tcx>,
                ctxt: CompilerCtxt<'_, $tcx>,
            ) -> bool {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.is_blocked_by(node, ctxt),
                    )+
                }
            }
        }

        impl<$tcx> $crate::borrow_pcg::edge_data::LabelEdgePlaces<$tcx> for $enum_name<$tcx> {
            fn label_blocked_places(
                &mut self,
                predicate: &$crate::borrow_pcg::edge_data::LabelNodePredicate<'tcx>,
                labeller: &impl $crate::borrow_pcg::has_pcs_elem::PlaceLabeller<'tcx>,
                ctxt: CompilerCtxt<'_, 'tcx>,
            ) -> $crate::utils::data_structures::HashSet<$crate::borrow_pcg::edge_data::NodeReplacement<'tcx>> {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.label_blocked_places(predicate, labeller, ctxt),
                    )+
                }
            }

            fn label_blocked_by_places(
                &mut self,
                predicate: &$crate::borrow_pcg::edge_data::LabelNodePredicate<'tcx>,
                labeller: &impl $crate::borrow_pcg::has_pcs_elem::PlaceLabeller<'tcx>,
                ctxt: CompilerCtxt<'_, 'tcx>,
            ) -> $crate::utils::data_structures::HashSet<$crate::borrow_pcg::edge_data::NodeReplacement<'tcx>> {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.label_blocked_by_places(predicate, labeller, ctxt),
                    )+
                }
            }
        }

        $(
            impl<$tcx> From<$inner_type> for $enum_name<$tcx> {
                fn from(inner: $inner_type) -> Self {
                    $enum_name::$variant_name(inner)
                }
            }
        )+

        impl<$tcx> $crate::borrow_pcg::edge_data::LabelEdgeLifetimeProjections<$tcx> for $enum_name<$tcx> {
            fn label_lifetime_projections(
                &mut self,
                predicate: &$crate::borrow_pcg::edge_data::LabelNodePredicate<'tcx>,
                label: Option<$crate::borrow_pcg::region_projection::LifetimeProjectionLabel>,
                ctxt: CompilerCtxt<'_, 'tcx>,
            ) -> $crate::borrow_pcg::has_pcs_elem::LabelLifetimeProjectionResult {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.label_lifetime_projections(predicate, label, ctxt),
                    )+
                }
            }
        }

        impl<$tcx> HasValidityCheck<'_, $tcx> for $enum_name<$tcx> {
            fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.check_validity(ctxt),
                    )+
                }
            }
        }

        impl<'a, $tcx: 'a, Ctxt: $crate::HasBorrowCheckerCtxt<'a, $tcx>> $crate::utils::display::DisplayWithCtxt<Ctxt> for $enum_name<$tcx> {
            fn display_output(&self, ctxt: Ctxt, mode: $crate::utils::display::OutputMode) -> $crate::utils::display::DisplayOutput {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.display_output(ctxt, mode),
                    )+
                }
            }
        }
    }
}
pub(crate) use edgedata_enum;
