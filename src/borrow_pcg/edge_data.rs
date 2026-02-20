use crate::{
    borrow_pcg::{
        borrow_pcg_edge::BorrowPcgEdgeRef,
        edge::kind::{BorrowPcgEdgeKind, BorrowPcgEdgeType},
        graph::Conditioned,
        has_pcs_elem::{LabelNodeContext, LabelPlace, PlaceLabeller, SourceOrTarget},
        region_projection::{
            LifetimeProjection, LifetimeProjectionLabel, OverrideRegionDebugString,
            PcgLifetimeProjectionBase, RegionIdx,
        },
    },
    pcg::{
        LabelPlaceConditionally, MaybeHasLocation, PcgNode, PcgNodeLike, PcgNodeType,
        PcgNodeWithPlace,
    },
    utils::{
        HasBorrowCheckerCtxt, PcgNodeComponent, PcgPlace, Place, PrefixRelation, SnapshotLocation,
        data_structures::HashSet,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        maybe_old::MaybeLabelledPlace,
    },
};

use super::borrow_pcg_edge::{BlockedNode, LocalNode};

/// A trait for data that represents a hyperedge in the Borrow PCG.
pub trait EdgeData<'tcx, Ctxt: Copy, P: Copy + PartialEq = Place<'tcx>> {
    /// For an edge A -> B, this returns the set of nodes A. In general, the capabilities
    /// of nodes B are obtained from these nodes.
    fn blocked_nodes<'slf>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Box<dyn std::iter::Iterator<Item = BlockedNode<'tcx, P>> + 'slf>
    where
        'tcx: 'slf;

    /// For an edge A -> B, this returns the set of nodes B. In general, these nodes
    /// obtain their capabilities from the nodes A.
    fn blocked_by_nodes<'slf>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx, P>> + 'slf>
    where
        'tcx: 'slf;

    fn blocks_node(&self, node: BlockedNode<'tcx, P>, ctxt: Ctxt) -> bool {
        self.blocked_nodes(ctxt).any(|n| n == node)
    }

    fn is_blocked_by(&self, node: LocalNode<'tcx, P>, ctxt: Ctxt) -> bool {
        self.blocked_by_nodes(ctxt).any(|n| n == node)
    }

    fn nodes<'slf>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Box<
        dyn std::iter::Iterator<
                Item = PcgNode<
                    'tcx,
                    MaybeLabelledPlace<'tcx, P>,
                    PcgLifetimeProjectionBase<'tcx, P>,
                >,
            > + 'slf,
    >
    where
        'tcx: 'slf,
        P: 'slf,
    {
        Box::new(
            self.blocked_nodes(ctxt)
                .chain(self.blocked_by_nodes(ctxt).map(std::convert::Into::into)),
        )
    }

    fn references_place(&self, place: P, ctxt: Ctxt) -> bool {
        self.nodes(ctxt).any(|n| match n {
            PcgNode::Place(p) => p.as_current_place() == Some(place),
            PcgNode::LifetimeProjection(rp) => rp.base.as_current_place() == Some(place),
        })
    }
}

impl<'tcx, Ctxt: Copy, C, P: PcgNodeComponent> EdgeData<'tcx, Ctxt, P>
    for Conditioned<BorrowPcgEdgeKind<'tcx, P>, C>
where
    BorrowPcgEdgeKind<'tcx, P>: EdgeData<'tcx, Ctxt, P>,
{
    fn blocked_nodes<'slf>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Box<dyn std::iter::Iterator<Item = BlockedNode<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        self.value.blocked_nodes(ctxt)
    }

    fn blocked_by_nodes<'slf>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        self.value.blocked_by_nodes(ctxt)
    }

    fn blocks_node(&self, node: BlockedNode<'tcx, P>, ctxt: Ctxt) -> bool {
        self.value.blocks_node(node, ctxt)
    }

    fn is_blocked_by(&self, node: LocalNode<'tcx, P>, ctxt: Ctxt) -> bool {
        self.value.is_blocked_by(node, ctxt)
    }

    fn nodes<'slf>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Box<
        dyn std::iter::Iterator<
                Item = PcgNode<
                    'tcx,
                    MaybeLabelledPlace<'tcx, P>,
                    PcgLifetimeProjectionBase<'tcx, P>,
                >,
            > + 'slf,
    >
    where
        'tcx: 'slf,
        P: 'slf,
    {
        Box::new(
            self.blocked_nodes(ctxt)
                .chain(self.blocked_by_nodes(ctxt).map(std::convert::Into::into)),
        )
    }

    fn references_place(&self, place: P, ctxt: Ctxt) -> bool {
        self.nodes(ctxt).any(|n| match n {
            PcgNode::Place(p) => p.as_current_place() == Some(place),
            PcgNode::LifetimeProjection(rp) => rp.base.as_current_place() == Some(place),
        })
    }
}

impl<'tcx, Ctxt: Copy> EdgeData<'tcx, Ctxt> for BorrowPcgEdgeRef<'tcx, '_>
where
    BorrowPcgEdgeKind<'tcx>: EdgeData<'tcx, Ctxt>,
{
    fn blocked_nodes<'slf>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Box<dyn std::iter::Iterator<Item = BlockedNode<'tcx, Place<'tcx>>> + 'slf>
    where
        'tcx: 'slf,
    {
        self.kind().blocked_nodes(ctxt)
    }

    fn blocked_by_nodes<'slf>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx, Place<'tcx>>> + 'slf>
    where
        'tcx: 'slf,
    {
        self.kind().blocked_by_nodes(ctxt)
    }

    fn blocks_node(&self, node: BlockedNode<'tcx, Place<'tcx>>, ctxt: Ctxt) -> bool {
        self.kind().blocks_node(node, ctxt)
    }

    fn is_blocked_by(&self, node: LocalNode<'tcx, Place<'tcx>>, ctxt: Ctxt) -> bool {
        self.kind().is_blocked_by(node, ctxt)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LabelNodePredicate<'tcx, P = Place<'tcx>> {
    LifetimeProjectionLabelEquals(Option<LifetimeProjectionLabel>),
    PlaceLabelEquals(Option<SnapshotLocation>),
    ProjectionRegionIdxEquals(RegionIdx),
    Equals(PcgNodeWithPlace<'tcx, P>),
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

impl<P: Copy> LabelNodePredicate<'_, P> {
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
}

impl<'tcx, P: PcgNodeComponent> LabelNodePredicate<'tcx, P> {
    /// Creates a predicate that matches exactly the given lifetime projection.
    pub(crate) fn equals_lifetime_projection(
        projection: LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx, P>>,
    ) -> Self {
        Self::Equals(PcgNode::LifetimeProjection(projection.rebase()))
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx> + OverrideRegionDebugString>
    DisplayWithCtxt<Ctxt> for LabelNodePredicate<'tcx>
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
                    &" && ".into(),
                ),
                ")".into(),
            ]),
            LabelNodePredicate::Or(predicates) => DisplayOutput::Seq(vec![
                "(".into(),
                DisplayOutput::join(
                    predicates.iter().map(|p| p.display_output(ctxt, mode)),
                    &" || ".into(),
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

impl<'tcx, P: PcgNodeComponent + PrefixRelation> LabelNodePredicate<'tcx, P> {
    pub(crate) fn applies_to(
        &self,
        candidate: PcgNode<'tcx, MaybeLabelledPlace<'tcx, P>, PcgLifetimeProjectionBase<'tcx, P>>,
        label_context: LabelNodeContext,
    ) -> bool {
        let related_maybe_labelled_place = candidate.related_maybe_labelled_place();
        let related_place = related_maybe_labelled_place
            .map(super::super::utils::place::maybe_old::MaybeLabelledPlace::place);
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
pub struct NodeReplacement<'tcx, P = Place<'tcx>> {
    pub(crate) from: PcgNodeWithPlace<'tcx, P>,
    pub(crate) to: PcgNodeWithPlace<'tcx, P>,
}

impl<'tcx, P: Copy + Eq + std::hash::Hash> NodeReplacement<'tcx, P> {
    pub(crate) fn new(from: PcgNodeWithPlace<'tcx, P>, to: PcgNodeWithPlace<'tcx, P>) -> Self {
        Self { from, to }
    }
}

impl<'tcx, Ctxt: Copy, P: Eq + std::hash::Hash + DisplayWithCtxt<Ctxt>> DisplayWithCtxt<Ctxt>
    for NodeReplacement<'tcx, P>
where
    PcgNodeWithPlace<'tcx, P>: DisplayWithCtxt<Ctxt>,
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Seq(vec![
            self.from.display_output(ctxt, mode),
            " → ".into(),
            self.to.display_output(ctxt, mode),
        ])
    }
}

pub(crate) fn display_node_replacements<
    'a,
    'tcx: 'a,
    Ctxt: Copy,
    P: Eq + std::hash::Hash + DisplayWithCtxt<Ctxt>,
>(
    replacements: &HashSet<NodeReplacement<'tcx, P>>,
    ctxt: Ctxt,
    mode: OutputMode,
) -> DisplayOutput
where
    PcgNodeWithPlace<'tcx, P>: DisplayWithCtxt<Ctxt>,
{
    if replacements.is_empty() {
        return DisplayOutput::EMPTY;
    }
    let items: Vec<DisplayOutput> = replacements
        .iter()
        .map(|r| r.display_output(ctxt, mode))
        .collect();
    DisplayOutput::Seq(vec![
        "Labelled nodes: [".into(),
        DisplayOutput::join(items, &", ".into()),
        "]".into(),
    ])
}

pub(crate) fn conditionally_label_places<
    'pcg,
    'tcx,
    Ctxt: Copy,
    P: PcgPlace<'tcx, Ctxt>,
    Node: PcgNodeLike<'tcx, Ctxt, P> + LabelPlace<'tcx, Ctxt, P> + 'pcg,
>(
    nodes: impl IntoIterator<Item = &'pcg mut Node>,
    predicate: &LabelNodePredicate<'tcx, P>,
    labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
    label_context: LabelNodeContext,
    ctxt: Ctxt,
) -> HashSet<NodeReplacement<'tcx, P>> {
    let mut result = HashSet::default();
    for node in nodes {
        node.label_place_conditionally(&mut result, predicate, labeller, label_context, ctxt);
    }
    result
}
pub trait LabelEdgePlaces<'tcx, Ctxt, P> {
    fn label_blocked_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>>;

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>>;
}

macro_rules! label_edge_places_wrapper {
    (
        $ty:ty
    ) => {
        impl<'tcx, Ctxt: DebugCtxt + Copy, P: $crate::utils::PcgPlace<'tcx, Ctxt>>
            LabelEdgePlaces<'tcx, Ctxt, P> for $ty
        where
            <Self as std::ops::Deref>::Target: LabelEdgePlaces<'tcx, Ctxt, P>,
        {
            fn label_blocked_places(
                &mut self,
                predicate: &LabelNodePredicate<'tcx, P>,
                labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
                ctxt: Ctxt,
            ) -> HashSet<NodeReplacement<'tcx, P>> {
                use std::ops::DerefMut;
                self.deref_mut()
                    .label_blocked_places(predicate, labeller, ctxt)
            }

            fn label_blocked_by_places(
                &mut self,
                predicate: &LabelNodePredicate<'tcx, P>,
                labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
                ctxt: Ctxt,
            ) -> HashSet<NodeReplacement<'tcx, P>> {
                use std::ops::DerefMut;
                self.deref_mut()
                    .label_blocked_by_places(predicate, labeller, ctxt)
            }
        }
    };
}

pub(crate) use label_edge_places_wrapper;

use super::has_pcs_elem::LabelLifetimeProjectionResult;

/// Trait for labeling lifetime projections on edges.
/// Checks the predicate and then applies the label operation if it matches.
/// Analogous to `LabelEdgePlaces` for places.
pub trait LabelEdgeLifetimeProjections<'tcx, Ctxt, P> {
    fn label_lifetime_projections(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: Ctxt,
    ) -> LabelLifetimeProjectionResult;
}

macro_rules! label_edge_lifetime_projections_wrapper {
    (
        $ty:ty
    ) => {
        impl<'tcx, Ctxt: DebugCtxt + Copy, P> LabelEdgeLifetimeProjections<'tcx, Ctxt, P> for $ty
        where
            <Self as std::ops::Deref>::Target: LabelEdgeLifetimeProjections<'tcx, Ctxt, P>,
        {
            fn label_lifetime_projections(
                &mut self,
                predicate: &LabelNodePredicate<'tcx, P>,
                label: Option<LifetimeProjectionLabel>,
                ctxt: Ctxt,
            ) -> LabelLifetimeProjectionResult {
                use std::ops::DerefMut;
                self.deref_mut()
                    .label_lifetime_projections(predicate, label, ctxt)
            }
        }
    };
}

pub(crate) use label_edge_lifetime_projections_wrapper;

macro_rules! edgedata_enum {
    (
        $enum_path:path,
        $enum_name:ident<'tcx, P>,
        $( $variant_name:ident($inner_type:ty) ),+ $(,)?
    ) => {
            mod generated_impls {
                use $enum_path;
                use $crate::borrow_pcg::borrow_pcg_edge::{BlockedNode, LocalNode};
                use $crate::borrow_pcg::edge_data::{EdgeData, LabelEdgePlaces, LabelEdgeLifetimeProjections};
                use $crate::utils::place::PcgPlace;
                use std::iter::Iterator;
            impl<'tcx,
                Ctxt: Copy,
                P: PcgPlace<'tcx, Ctxt>>
                EdgeData<'tcx, Ctxt, P> for $enum_name<'tcx, P> where $(
                    $inner_type: EdgeData<'tcx, Ctxt, P>,
                )+ {
                fn blocked_nodes<'slf>(
                    &'slf self,
                    ctxt: Ctxt,
                ) -> Box<dyn Iterator<Item = BlockedNode<'tcx, P>> + 'slf>
                where
                    'tcx: 'slf,
                {
                    match self {
                        $(
                            $enum_name::$variant_name(inner) => inner.blocked_nodes(ctxt),
                        )+
                    }
                }

                fn blocked_by_nodes<'slf>(
                    &'slf self,
                    ctxt: Ctxt,
                ) -> Box<dyn Iterator<Item = LocalNode<'tcx, P>> + 'slf>
                where
                    'tcx: 'slf,
                {
                    match self {
                        $(
                            $enum_name::$variant_name(inner) => inner.blocked_by_nodes(ctxt),
                        )+
                    }
                }

                fn blocks_node<'slf>(
                    &self,
                    node: BlockedNode<'tcx, P>,
                    ctxt: Ctxt,
                ) -> bool {
                    match self {
                        $(
                            $enum_name::$variant_name(inner) => inner.blocks_node(node, ctxt),
                        )+
                    }
                }

                fn is_blocked_by<'slf>(
                    &self,
                    node: LocalNode<'tcx, P>,
                    ctxt: Ctxt,
                ) -> bool {
                    match self {
                        $(
                            $enum_name::$variant_name(inner) => inner.is_blocked_by(node, ctxt),
                        )+
                    }
                }
            }

            use $crate::borrow_pcg::has_pcs_elem::PlaceLabeller;
            use $crate::borrow_pcg::edge_data::{LabelNodePredicate, NodeReplacement};
            use $crate::utils::data_structures::HashSet;

            impl<'tcx, Ctxt: $crate::utils::DebugCtxt + Copy, P: PcgPlace<'tcx, Ctxt>> LabelEdgePlaces<'tcx, Ctxt, P> for $enum_name<'tcx, P> where $(
                $inner_type: LabelEdgePlaces<'tcx, Ctxt, P>,
            )+ {
                fn label_blocked_places(
                    &mut self,
                    predicate: &LabelNodePredicate<'tcx, P>,
                    labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
                    ctxt: Ctxt
                ) -> HashSet<NodeReplacement<'tcx, P>> {
                    match self {
                        $(
                            $enum_name::$variant_name(inner) => inner.label_blocked_places(predicate, labeller, ctxt),
                        )+
                    }
                }

                fn label_blocked_by_places(
                    &mut self,
                    predicate: &LabelNodePredicate<'tcx, P>,
                    labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
                    ctxt: Ctxt
                ) -> HashSet<NodeReplacement<'tcx, P>> {
                    match self {
                        $(
                            $enum_name::$variant_name(inner) =>
                                inner.label_blocked_by_places(predicate, labeller, ctxt),
                        )+
                    }
                }
            }

            $(
                impl<'tcx, P> From<$inner_type> for $enum_name<'tcx, P> {
                    fn from(inner: $inner_type) -> Self {
                        $enum_name::$variant_name(inner)
                    }
                }
            )+

            use $crate::borrow_pcg::region_projection::LifetimeProjectionLabel;
            use $crate::borrow_pcg::has_pcs_elem::LabelLifetimeProjectionResult;

            impl<'tcx, Ctxt: $crate::utils::DebugCtxt + Copy, P: PcgPlace<'tcx, Ctxt>> LabelEdgeLifetimeProjections<'tcx, Ctxt, P> for $enum_name<'tcx, P> where $(
                $inner_type: LabelEdgeLifetimeProjections<'tcx, Ctxt, P>,
            )+ {
                fn label_lifetime_projections(
                    &mut self,
                    predicate: &LabelNodePredicate<'tcx, P>,
                    label: Option<LifetimeProjectionLabel>,
                    ctxt: Ctxt,
                ) -> LabelLifetimeProjectionResult {
                    match self {
                        $(
                            $enum_name::$variant_name(inner) =>
                                inner.label_lifetime_projections(predicate, label, ctxt),
                        )+
                    }
                }
            }

            use $crate::HasValidityCheck;

            impl<'tcx, Ctxt: Copy + $crate::utils::DebugCtxt, P: PcgPlace<'tcx, Ctxt>> HasValidityCheck<Ctxt> for $enum_name<'tcx, P> where $(
                $inner_type: HasValidityCheck<Ctxt>,
            )+ {
                fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
                    match self {
                        $(
                            $enum_name::$variant_name(inner) => inner.check_validity(ctxt),
                        )+
                    }
                }
            }
        }
    }
}
pub(crate) use edgedata_enum;
