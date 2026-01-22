//! Borrow-flow edges
use std::marker::PhantomData;

use serde_derive::Serialize;

use crate::{
    borrow_pcg::{
        borrow_pcg_edge::{BlockedNode, LocalNode},
        edge::kind::BorrowPcgEdgeType,
        edge_data::{
            EdgeData, LabelEdgeLifetimeProjections, LabelEdgePlaces, LabelNodePredicate,
            NodeReplacement, conditionally_label_places,
        },
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionResult, LabelNodeContext,
            PlaceLabeller, SourceOrTarget,
        },
        region_projection::{
            LifetimeProjection, LifetimeProjectionLabel, LocalLifetimeProjection,
            LocalLifetimeProjectionBase, PcgLifetimeProjectionBase, PcgLifetimeProjectionBaseLike,
        },
    },
    pcg::{LabelPlaceConditionally, PcgNode, PcgNodeLike},
    pcg_validity_assert,
    rustc_interface::middle::{mir, ty},
    utils::{
        CompilerCtxt, DebugCtxt, DebugRepr, HasBorrowCheckerCtxt, HasCompilerCtxt, Place,
        PrefixRelation,
        data_structures::HashSet,
        display::{DisplayOutput, DisplayWithCompilerCtxt, DisplayWithCtxt, OutputMode},
        maybe_old::MaybeLabelledPlace,
        validity::HasValidityCheck,
    },
};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct BorrowFlowEdge<'tcx, P = Place<'tcx>> {
    source: LifetimeProjection<'tcx, PcgLifetimeProjectionBase<'tcx, P>>,
    pub(crate) target: LocalLifetimeProjection<'tcx, P>,
    pub(crate) kind: BorrowFlowEdgeKind<'tcx>,
}

impl<'tcx, P> BorrowFlowEdge<'tcx, P> {
    pub(crate) fn future_edge_kind(self) -> Option<private::FutureEdgeKind> {
        if let BorrowFlowEdgeKind::Future(future_edge_kind) = self.kind {
            Some(future_edge_kind)
        } else {
            None
        }
    }
}

impl<'tcx, Ctxt: Copy + DebugCtxt, P: Eq + std::hash::Hash + Copy + PrefixRelation>
    LabelEdgePlaces<'tcx, Ctxt, P> for BorrowFlowEdge<'tcx, P>
where
    LifetimeProjection<'tcx, PcgLifetimeProjectionBase<'tcx, P>>:
        LabelPlaceConditionally<'tcx, Ctxt, P>,
    LocalLifetimeProjection<'tcx, P>: LabelPlaceConditionally<'tcx, Ctxt, P>,
{
    fn label_blocked_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>> {
        let future_edge_kind = self.future_edge_kind();
        conditionally_label_places(
            vec![&mut self.source],
            predicate,
            labeller,
            LabelNodeContext::new(
                SourceOrTarget::Source,
                BorrowPcgEdgeType::BorrowFlow { future_edge_kind },
            ),
            ctxt,
        )
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>> {
        let future_edge_kind = self.future_edge_kind();
        conditionally_label_places(
            vec![&mut self.target],
            predicate,
            labeller,
            LabelNodeContext::new(
                SourceOrTarget::Target,
                BorrowPcgEdgeType::BorrowFlow { future_edge_kind },
            ),
            ctxt,
        )
    }
}

impl<
    'a,
    'tcx,
    Ctxt: Copy + DebugCtxt,
    P: std::fmt::Debug + Eq + Copy + PrefixRelation + std::hash::Hash,
> LabelEdgeLifetimeProjections<'tcx, Ctxt, P> for BorrowFlowEdge<'tcx, P>
where
    Self: DisplayWithCtxt<Ctxt> + HasValidityCheck<Ctxt>,
    PcgLifetimeProjectionBase<'tcx, P>: PcgLifetimeProjectionBaseLike<'tcx>,
    LocalLifetimeProjectionBase<'tcx, P>: PcgLifetimeProjectionBaseLike<'tcx>,
{
    fn label_lifetime_projections(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: Ctxt,
    ) -> LabelLifetimeProjectionResult {
        tracing::debug!(
            "Labeling region projection: {} (predicate: {:?}, label: {:?})",
            self.display_string(ctxt),
            predicate,
            label
        );
        let edge_type = BorrowPcgEdgeType::BorrowFlow {
            future_edge_kind: self.future_edge_kind(),
        };
        let long_matches = predicate.applies_to(
            PcgNode::LifetimeProjection(self.source),
            LabelNodeContext::new(SourceOrTarget::Source, edge_type),
        );
        let short_matches = predicate.applies_to(
            PcgNode::LifetimeProjection(self.target.rebase()),
            LabelNodeContext::new(SourceOrTarget::Target, edge_type),
        );
        if long_matches && short_matches {
            return LabelLifetimeProjectionResult::ShouldCollapse;
        }
        let mut changed = LabelLifetimeProjectionResult::Unchanged;
        if long_matches {
            changed |= self.source.label_lifetime_projection(label);
        }
        if short_matches {
            changed |= self.target.label_lifetime_projection(label);
        }
        self.assert_validity(ctxt);
        changed
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for BorrowFlowEdge<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        let type_annotation = match self.kind {
            BorrowFlowEdgeKind::Assignment(assignment_data)
                if let Some(cast) = assignment_data.cast =>
            {
                format!(" with cast {:?}", cast.kind)
            }
            _ => String::new(),
        };
        DisplayOutput::Text(
            format!(
                "{} -> {}{}",
                DisplayWithCtxt::<_>::display_string(&self.source, ctxt),
                self.target.display_string(ctxt),
                type_annotation
            )
            .into(),
        )
    }
}

impl<'tcx, Ctxt, P: PartialEq + Copy> EdgeData<'tcx, Ctxt, P> for BorrowFlowEdge<'tcx, P>
where
    LifetimeProjection<'tcx, PcgLifetimeProjectionBase<'tcx, P>>: PcgNodeLike<'tcx, Ctxt, P>,
    LocalLifetimeProjection<'tcx, P>: PcgNodeLike<'tcx, Ctxt, P>,
{
    fn blocks_node<'slf>(&self, node: BlockedNode<'tcx, P>, ctxt: Ctxt) -> bool {
        self.source.to_pcg_node(ctxt) == node
    }

    fn blocked_nodes<'slf>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Box<dyn Iterator<Item = BlockedNode<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(std::iter::once(self.source.to_pcg_node(ctxt)))
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

impl<'a, 'tcx: 'a> HasValidityCheck<CompilerCtxt<'a, 'tcx>> for BorrowFlowEdge<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> Result<(), String> {
        self.source.check_validity(ctxt)?;
        self.target.check_validity(ctxt)?;
        if self.source.to_pcg_node(ctxt) == self.target.to_pcg_node(ctxt) {
            return Err(format!(
                "BorrowFlowEdge: long and short are the same node: {}",
                self.display_string(ctxt)
            ));
        }
        Ok(())
    }
}

impl<'tcx, P: Copy> BorrowFlowEdge<'tcx, P> {
    pub(crate) fn new(
        source: LifetimeProjection<'tcx, PcgLifetimeProjectionBase<'tcx, P>>,
        target: LocalLifetimeProjection<'tcx, P>,
        kind: BorrowFlowEdgeKind<'tcx>,
    ) -> Self {
        Self {
            source,
            target,
            kind,
        }
    }

    /// The blocked lifetime projection. Intuitively, it must outlive the `short()` projection.
    pub fn long(&self) -> LifetimeProjection<'tcx, PcgLifetimeProjectionBase<'tcx, P>> {
        self.source
    }

    /// The blocking lifetime projection. Intuitively, it must die before the `long()` projection.
    pub fn short(&self) -> LocalLifetimeProjection<'tcx, P> {
        self.target
    }

    pub fn kind(&self) -> BorrowFlowEdgeKind<'tcx> {
        self.kind
    }
}

impl<'tcx, Ty: serde::Serialize> serde::Serialize for CastData<'tcx, Ty> {
    fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        todo!()
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct CastData<'tcx, Ty = ty::Ty<'tcx>> {
    kind: mir::CastKind,
    ty: Ty,
    _phantom: PhantomData<&'tcx Ty>,
}

impl<'tcx, Ty> CastData<'tcx, Ty> {
    pub(crate) fn new(kind: mir::CastKind, ty: Ty) -> Self {
        Self {
            kind,
            ty,
            _phantom: PhantomData,
        }
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, Serialize)]
pub enum OperandType {
    Move,
    Copy,
    Const,
}

impl OperandType {
    pub fn is_place(self) -> bool {
        matches!(self, OperandType::Move | OperandType::Copy)
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, Serialize)]
pub struct AssignmentData<'tcx, Ty = ty::Ty<'tcx>> {
    operand_type: OperandType,
    cast: Option<CastData<'tcx, Ty>>,
}

impl<'tcx, Ty> AssignmentData<'tcx, Ty> {
    pub(crate) fn new(operand_type: OperandType, cast: Option<CastData<'tcx, Ty>>) -> Self {
        Self { operand_type, cast }
    }

    pub fn operand_type(&self) -> OperandType {
        self.operand_type
    }

    pub fn cast_kind(&self) -> Option<mir::CastKind> {
        self.cast.as_ref().map(|cd| cd.kind)
    }
}

pub(crate) mod private {
    use serde_derive::Serialize;

    #[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, Serialize)]
    pub enum FutureEdgeKind {
        /// An edge of the form `x.f|'a -> x|'a at FUTURE`
        FromExpansion,

        /// For a borrow e.g. let y = &mut x, an edge of the form `y|'a -> x|'a at FUTURE`
        FromBorrow,

        /// For an expansion, an edge of the form `x|'a at loc -> x|'a at FUTURE`
        ToFutureSelf,
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, Serialize)]
pub enum BorrowFlowEdgeKind<'tcx, Ty = ty::Ty<'tcx>> {
    /// Indicates that the borrow flows to the `target_rp_index`th region
    /// projection of the `field_idx`th field of the aggregate.
    ///
    /// Introduced in the following two cases:
    /// 1. Collapsing an owned place: edges flow from the (labelled) expansions
    ///    of the place to the current base
    /// 2. Assigning an aggregate (e.g. `x = Aggregate(a, b)`): edges flow from
    ///    the (labelled) arguments to the rvalue to lifetime projections of `x`
    ///
    /// TODO: Perhaps a different kind for the 1st case? We don't need this metadata I think
    Aggregate {
        field_idx: usize,
        target_rp_index: usize,
    },
    /// For a borrow `let x: &'x T<'b> = &y`, where y is of typ T<'a>, an edge generated
    /// for `{y|'a} -> {x|'b}` of this kind is created if 'a outlives 'b.
    ///
    BorrowOutlives {
        /// If true, the lifetimes are equal (mutually outlive each other),
        /// false otherwise.
        ///
        /// This field is somewhat redundant because the equality can be queried
        /// by the borrow checker based on the regions of the long and short
        /// endpoints. However, it is useful for clients that may not have access
        /// to the borrow checker (e.g. visualization tools).
        regions_equal: bool,
    },
    InitialBorrows,
    /// Borrows that have flowed from a place as the result of a MIR assignment
    /// statement. For a statement e.g. `let x = e`, borrows will flow from the
    /// lifetime projections in `e` to the lifetime projections of `x`.
    Assignment(AssignmentData<'tcx, Ty>),
    Future(private::FutureEdgeKind),
}

impl<'tcx, Ctxt> DebugRepr<Ctxt> for BorrowFlowEdgeKind<'tcx> {
    type Repr = BorrowFlowEdgeKind<'tcx, String>;
    fn debug_repr(&self, _ctxt: Ctxt) -> Self::Repr {
        match self {
            BorrowFlowEdgeKind::Aggregate {
                field_idx,
                target_rp_index,
            } => BorrowFlowEdgeKind::Aggregate {
                field_idx: *field_idx,
                target_rp_index: *target_rp_index,
            },
            BorrowFlowEdgeKind::BorrowOutlives {
                regions_equal: lifetimes_equal,
            } => BorrowFlowEdgeKind::BorrowOutlives {
                regions_equal: *lifetimes_equal,
            },
            BorrowFlowEdgeKind::InitialBorrows => BorrowFlowEdgeKind::InitialBorrows,
            BorrowFlowEdgeKind::Future(future_edge_kind) => {
                BorrowFlowEdgeKind::Future(*future_edge_kind)
            }
            BorrowFlowEdgeKind::Assignment(assignment_data) => {
                BorrowFlowEdgeKind::Assignment(AssignmentData::new(
                    assignment_data.operand_type,
                    assignment_data
                        .cast
                        .map(|cast| CastData::new(cast.kind, format!("{:?}", cast.ty))),
                ))
            }
        }
    }
}

impl<'tcx, Ty: std::fmt::Debug> std::fmt::Display for BorrowFlowEdgeKind<'tcx, Ty> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BorrowFlowEdgeKind::Aggregate {
                field_idx,
                target_rp_index,
            } => write!(f, "Aggregate({field_idx}, {target_rp_index})"),
            BorrowFlowEdgeKind::BorrowOutlives {
                regions_equal: lifetimes_equal,
            } => {
                if *lifetimes_equal {
                    write!(f, "equals")
                } else {
                    write!(f, "outlives")
                }
            }
            BorrowFlowEdgeKind::InitialBorrows => write!(f, "InitialBorrows"),
            BorrowFlowEdgeKind::Future(_) => write!(f, "Future"),
            BorrowFlowEdgeKind::Assignment(assignment_data) => {
                let first_part = match assignment_data.operand_type {
                    OperandType::Move => "Move",
                    OperandType::Copy => "Copy",
                    OperandType::Const => "Const",
                };
                let second_part = match &assignment_data.cast {
                    Some(cast) => format!(" with cast {:?}", cast.kind),
                    None => String::new(),
                };
                write!(f, "{first_part}{second_part}")
            }
        }
    }
}
