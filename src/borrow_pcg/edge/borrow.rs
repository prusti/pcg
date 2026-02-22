//! Borrow edges
use crate::{
    borrow_pcg::{
        edge::kind::BorrowPcgEdgeType,
        edge_data::{
            LabelEdgeLifetimeProjections, LabelEdgePlaces, LabelNodePredicate, NodeReplacement,
            conditionally_label_places,
        },
        has_pcs_elem::{
            LabelLifetimeProjectionResult, LabelNodeContext, LabelPlace, PlaceLabeller,
            SourceOrTarget,
        },
        region_projection::LifetimeProjectionLabel,
    },
    pcg::{PcgNode, PcgNodeLike, PcgNodeWithPlace},
    rustc_interface::{
        ast::Mutability,
        borrowck::BorrowIndex,
        middle::{
            mir::{self, Location},
            ty::{self},
        },
    },
    utils::{
        DebugCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, PcgPlace, Place,
        data_structures::HashSet,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
    },
};

use crate::{
    borrow_pcg::{
        borrow_pcg_edge::{BlockedNode, LocalNode},
        edge_data::EdgeData,
        region_projection::LifetimeProjection,
    },
    utils::{CompilerCtxt, place::maybe_old::MaybeLabelledPlace, validity::HasValidityCheck},
};

/// A borrow that is explicit in the MIR (e.g. `let x = &mut y;`)
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct BorrowEdge<'tcx, P = Place<'tcx>> {
    /// The place that is blocked by the borrow, e.g. the y in `let x = &mut y;`
    pub(crate) blocked_place: MaybeLabelledPlace<'tcx, P>,
    /// The place that is assigned by the borrow, e.g. the x in `let x = &mut y;`
    pub(crate) assigned_ref: MaybeLabelledPlace<'tcx, P>,
    kind: mir::BorrowKind,

    /// The location when the borrow was created
    reserve_location: Location,

    pub(crate) region: ty::Region<'tcx>,

    // For some reason this may not be defined for certain shared borrows
    borrow_index: Option<BorrowIndex>,

    assigned_lifetime_projection_label: Option<LifetimeProjectionLabel>,

    pub(crate) activated: bool,
}

impl<'tcx, Ctxt: DebugCtxt + Copy, P: PcgPlace<'tcx, Ctxt>>
    LabelEdgeLifetimeProjections<'tcx, Ctxt, P> for BorrowEdge<'tcx, P>
{
    fn label_lifetime_projections(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: Ctxt,
    ) -> LabelLifetimeProjectionResult {
        let mut changed = LabelLifetimeProjectionResult::Unchanged;
        if predicate.applies_to(
            PcgNode::LifetimeProjection(self.assigned_lifetime_projection(ctxt).rebase()),
            LabelNodeContext::new(SourceOrTarget::Target, BorrowPcgEdgeType::Borrow),
        ) {
            self.assigned_lifetime_projection_label = label;
            changed = LabelLifetimeProjectionResult::Changed;
        }
        changed
    }
}

impl<'tcx, Ctxt: DebugCtxt + Copy, P: PcgPlace<'tcx, Ctxt>> LabelEdgePlaces<'tcx, Ctxt, P>
    for BorrowEdge<'tcx, P>
where
    MaybeLabelledPlace<'tcx, P>: LabelPlace<'tcx, Ctxt, P>,
    MaybeLabelledPlace<'tcx, P>: PcgNodeLike<'tcx, Ctxt, P>,
    LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx, P>>: PcgNodeLike<'tcx, Ctxt, P>,
{
    fn label_blocked_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>> {
        conditionally_label_places(
            vec![&mut self.blocked_place],
            predicate,
            labeller,
            LabelNodeContext::new(SourceOrTarget::Source, BorrowPcgEdgeType::Borrow),
            ctxt,
        )
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>> {
        let mut result = HashSet::default();
        let initial_assigned_lifetime_projection = self.assigned_lifetime_projection(ctxt);
        let from: PcgNodeWithPlace<'tcx, P> =
            PcgNode::LifetimeProjection(initial_assigned_lifetime_projection.rebase());
        let node_context = LabelNodeContext::new(SourceOrTarget::Target, BorrowPcgEdgeType::Borrow);
        if predicate.applies_to(from, node_context) {
            let changed = self.assigned_ref.label_place(labeller, ctxt);
            if changed {
                result.insert(NodeReplacement::new(
                    from,
                    self.assigned_lifetime_projection(ctxt).to_pcg_node(ctxt),
                ));
            }
        }
        result
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx> + DebugCtxt> HasValidityCheck<Ctxt>
    for BorrowEdge<'tcx>
{
    fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
        self.blocked_place.check_validity(ctxt)?;
        self.assigned_ref.check_validity(ctxt)?;
        Ok(())
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt> for BorrowEdge<'tcx> {
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        let rp_part = if let Some(rp) = self.assigned_lifetime_projection_label {
            format!(" <{}>", rp.display_output((), mode).into_text())
        } else {
            String::new()
        };
        DisplayOutput::Text(
            format!(
                "borrow: {}{} = &{} {}",
                self.assigned_ref.display_output(ctxt, mode).into_text(),
                rp_part,
                if self.kind.mutability() == Mutability::Mut {
                    "mut "
                } else {
                    ""
                },
                self.blocked_place.display_output(ctxt, mode).into_text(),
            )
            .into(),
        )
    }
}

impl<'tcx, Ctxt: Copy, P: PcgPlace<'tcx, Ctxt>> EdgeData<'tcx, Ctxt, P> for BorrowEdge<'tcx, P> {
    fn blocks_node<'slf>(&self, node: BlockedNode<'tcx, P>, _ctxt: Ctxt) -> bool {
        match node {
            PcgNode::Place(p) => self.blocked_place == p,
            _ => false,
        }
    }

    fn is_blocked_by<'slf>(&self, node: LocalNode<'tcx, P>, ctxt: Ctxt) -> bool {
        match node {
            PcgNode::Place(_) => false,
            PcgNode::LifetimeProjection(region_projection) => {
                region_projection == self.assigned_lifetime_projection(ctxt)
            }
        }
    }

    fn blocked_nodes<'slf>(
        &'slf self,
        _ctxt: Ctxt,
    ) -> Box<dyn Iterator<Item = BlockedNode<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(std::iter::once(self.blocked_place.into()))
    }

    fn blocked_by_nodes<'slf>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Box<dyn Iterator<Item = LocalNode<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        let rp = self.assigned_lifetime_projection(ctxt);
        Box::new(std::iter::once(LocalNode::LifetimeProjection(rp)))
    }
}

impl<'tcx> BorrowEdge<'tcx> {
    pub(crate) fn borrow_index(&self) -> Option<BorrowIndex> {
        self.borrow_index
    }

    #[must_use]
    pub fn region(&self) -> ty::Region<'tcx> {
        self.region
    }

    #[must_use]
    pub fn kind(&self) -> mir::BorrowKind {
        self.kind
    }

    #[must_use]
    pub fn assigned_ref(&self) -> MaybeLabelledPlace<'tcx> {
        self.assigned_ref
    }

    #[must_use]
    pub fn blocked_place(&self) -> MaybeLabelledPlace<'tcx> {
        self.blocked_place
    }

    pub(crate) fn new<'a>(
        blocked_place: MaybeLabelledPlace<'tcx>,
        assigned_place: MaybeLabelledPlace<'tcx>,
        kind: mir::BorrowKind,
        reservation_location: Location,
        region: ty::Region<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Self
    where
        'tcx: 'a,
    {
        assert!(assigned_place.ty(ctxt).ty.ref_mutability().is_some());
        let borrow = Self {
            blocked_place,
            assigned_ref: assigned_place,
            kind,
            reserve_location: reservation_location,
            region,
            assigned_lifetime_projection_label: None,
            borrow_index: ctxt.bc().region_to_borrow_index(region.into()),
            activated: !kind.is_two_phase_borrow(),
        };
        borrow.assert_validity(ctxt.bc_ctxt());
        borrow
    }

    pub(crate) fn reserve_location(&self) -> Location {
        self.reserve_location
    }

    pub(crate) fn effective_mutability(&self) -> Mutability {
        if self.activated {
            self.kind.mutability()
        } else {
            Mutability::Not
        }
    }

    /// The deref of the assigned place of the borrow. For example, if the borrow is
    /// `let x = &mut y;`, then the deref place is `*x`.
    #[must_use]
    pub fn deref_place(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> MaybeLabelledPlace<'tcx> {
        self.assigned_ref.project_deref(ctxt).unwrap()
    }
}
impl<'tcx, P: Copy + std::fmt::Debug> BorrowEdge<'tcx, P> {
    /// The region projection associated with the *type* of the assigned place
    /// of the borrow. For example in `let x: &'x mut i32 = ???`, the assigned
    /// region projection is `x↓'x`.
    pub(crate) fn assigned_lifetime_projection<Ctxt: Copy>(
        &self,
        ctxt: Ctxt,
    ) -> LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx, P>>
    where
        P: PcgPlace<'tcx, Ctxt>,
    {
        let assigned_ref_ty = self.assigned_ref.place().rust_ty(ctxt);
        match assigned_ref_ty.kind() {
            ty::TyKind::Ref(region, _, _) => LifetimeProjection::new(
                self.assigned_ref,
                (*region).into(),
                self.assigned_lifetime_projection_label,
                ctxt,
            )
            .unwrap_or_else(|| {
                panic!("No region idx for {:?} in {:?}", region, assigned_ref_ty,);
            }),
            other => unreachable!("{:?}", other),
        }
    }
}

impl std::fmt::Display for BorrowEdge<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "borrow blocking {} assigned to {}",
            self.blocked_place, self.assigned_ref,
        )
    }
}
