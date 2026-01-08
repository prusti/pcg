//! Borrow-flow edges
use std::marker::PhantomData;

use serde_derive::Serialize;

use crate::{
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        edge::kind::BorrowPcgEdgeType,
        edge_data::{
            EdgeData, LabelEdgeLifetimeProjections, LabelEdgePlaces, LabelNodePredicate,
            NodeReplacement, conditionally_label_places,
        },
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionResult, LabelNodeContext,
            PlaceLabeller, SourceOrTarget,
        },
        region_projection::{LifetimeProjection, LifetimeProjectionLabel, LocalLifetimeProjection},
    },
    pcg::{PcgNode, PcgNodeLike},
    pcg_validity_assert,
    rustc_interface::middle::{mir, ty},
    utils::{
        CompilerCtxt, DebugRepr, HasBorrowCheckerCtxt, HasCompilerCtxt,
        data_structures::HashSet,
        display::{DisplayOutput, DisplayWithCompilerCtxt, DisplayWithCtxt, OutputMode},
        validity::HasValidityCheck,
    },
};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct BorrowFlowEdge<'tcx> {
    source: LifetimeProjection<'tcx>,
    pub(crate) short: LocalLifetimeProjection<'tcx>,
    pub(crate) kind: BorrowFlowEdgeKind<'tcx>,
}

impl<'tcx> BorrowFlowEdge<'tcx> {
    pub(crate) fn future_edge_kind(self) -> Option<private::FutureEdgeKind> {
        if let BorrowFlowEdgeKind::Future(future_edge_kind) = self.kind {
            Some(future_edge_kind)
        } else {
            None
        }
    }
}

impl<'tcx> LabelEdgePlaces<'tcx> for BorrowFlowEdge<'tcx> {
    fn label_blocked_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> HashSet<NodeReplacement<'tcx>> {
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
        predicate: &LabelNodePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> HashSet<NodeReplacement<'tcx>> {
        let future_edge_kind = self.future_edge_kind();
        conditionally_label_places(
            vec![&mut self.short],
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

impl<'tcx> LabelEdgeLifetimeProjections<'tcx> for BorrowFlowEdge<'tcx> {
    fn label_lifetime_projections(
        &mut self,
        predicate: &LabelNodePredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
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
            PcgNode::LifetimeProjection(self.short.rebase()),
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
            changed |= self.short.label_lifetime_projection(label);
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
                self.short.display_string(ctxt),
                type_annotation
            )
            .into(),
        )
    }
}

impl<'tcx> EdgeData<'tcx> for BorrowFlowEdge<'tcx> {
    fn blocks_node<'slf>(&self, node: PcgNode<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.source.to_pcg_node(ctxt) == node
    }

    fn blocked_nodes<'slf, BC: Copy>(
        &'slf self,
        ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn Iterator<Item = PcgNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(std::iter::once(self.source.to_pcg_node(ctxt.ctxt())))
    }

    fn blocked_by_nodes<'slf, 'mir: 'slf, BC: Copy>(
        &'slf self,
        _ctxt: CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<dyn Iterator<Item = LocalNode<'tcx>> + 'slf>
    where
        'tcx: 'mir,
    {
        Box::new(std::iter::once(self.short.into()))
    }
}

impl<'tcx> HasValidityCheck<'_, 'tcx> for BorrowFlowEdge<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.source.check_validity(ctxt)?;
        self.short.check_validity(ctxt)?;
        if self.source.to_pcg_node(ctxt) == self.short.to_pcg_node(ctxt) {
            return Err(format!(
                "BorrowFlowEdge: long and short are the same node: {}",
                self.display_string(ctxt)
            ));
        }
        Ok(())
    }
}

impl<'tcx> BorrowFlowEdge<'tcx> {
    pub(crate) fn new<'a>(
        long: LifetimeProjection<'tcx>,
        short: LocalLifetimeProjection<'tcx>,
        kind: BorrowFlowEdgeKind<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Self
    where
        'tcx: 'a,
    {
        pcg_validity_assert!(long.to_pcg_node(ctxt.ctxt()) != short.to_pcg_node(ctxt.ctxt()));
        Self {
            source: long,
            short,
            kind,
        }
    }

    /// The blocked lifetime projection. Intuitively, it must outlive the `short()` projection.
    pub fn long(&self) -> LifetimeProjection<'tcx> {
        self.source
    }

    /// The blocking lifetime projection. Intuitively, it must die before the `long()` projection.
    pub fn short(&self) -> LocalLifetimeProjection<'tcx> {
        self.short
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
}

pub(crate) mod private {
    use serde_derive::Serialize;

    #[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, Serialize)]
    pub enum FutureEdgeKind {
        FromExpansion,
        FromBorrow,
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
