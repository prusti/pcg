//! Borrow edges
use crate::{
    borrow_pcg::{
        edge_data::{LabelEdgePlaces, LabelPlacePredicate},
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionPredicate,
            LabelLifetimeProjectionResult, LabelNodeContext, LabelPlaceWithContext, PlaceLabeller,
        },
        region_projection::LifetimeProjectionLabel,
    },
    pcg::PcgNode,
    rustc_interface::{
        ast::Mutability,
        borrowck::BorrowIndex,
        middle::{
            mir::{self, Location},
            ty::{self},
        },
    },
    utils::{
        HasBorrowCheckerCtxt, HasCompilerCtxt,
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
pub struct BorrowEdge<'tcx> {
    /// The place that is blocked by the borrow, e.g. the y in `let x = &mut y;`
    pub(crate) blocked_place: MaybeLabelledPlace<'tcx>,
    /// The place that is assigned by the borrow, e.g. the x in `let x = &mut y;`
    pub(crate) assigned_ref: MaybeLabelledPlace<'tcx>,
    kind: mir::BorrowKind,

    /// The location when the borrow was created
    reserve_location: Location,

    pub(crate) region: ty::Region<'tcx>,

    // For some reason this may not be defined for certain shared borrows
    borrow_index: Option<BorrowIndex>,

    assigned_lifetime_projection_label: Option<LifetimeProjectionLabel>,
}

impl<'a, 'tcx> LabelLifetimeProjection<'a, 'tcx> for BorrowEdge<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        predicate: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        let mut changed = LabelLifetimeProjectionResult::Unchanged;
        if predicate.matches(self.assigned_lifetime_projection(ctxt).rebase(), ctxt) {
            self.assigned_lifetime_projection_label = label;
            changed = LabelLifetimeProjectionResult::Changed;
        }
        changed
    }
}

impl<'tcx> LabelEdgePlaces<'tcx> for BorrowEdge<'tcx> {
    fn label_blocked_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.blocked_place.label_place_with_context(
            predicate,
            labeller,
            LabelNodeContext::for_node(self.blocked_place, false),
            ctxt,
        )
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        // Technically, `assigned_ref` does not block this node, but this place
        // is used to compute `assigned_region_projection` which *does* block this node
        // So we should label it
        self.assigned_ref.label_place_with_context(
            predicate,
            labeller,
            LabelNodeContext::for_node(self.assigned_ref, false),
            ctxt,
        )
    }
}

impl<'tcx> HasValidityCheck<'_, 'tcx> for BorrowEdge<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
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

impl<'tcx> EdgeData<'tcx> for BorrowEdge<'tcx> {
    fn blocks_node<'slf>(&self, node: BlockedNode<'tcx>, _ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        match node {
            PcgNode::Place(p) => self.blocked_place == p,
            _ => false,
        }
    }

    fn is_blocked_by<'slf>(&self, node: LocalNode<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        match node {
            PcgNode::Place(_) => false,
            PcgNode::LifetimeProjection(region_projection) => {
                region_projection == self.assigned_lifetime_projection(ctxt)
            }
        }
    }

    fn blocked_nodes<'slf, BC: Copy>(
        &'slf self,
        _ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn Iterator<Item = BlockedNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(std::iter::once(self.blocked_place.into()))
    }

    fn blocked_by_nodes<'slf, 'mir: 'slf, BC: Copy>(
        &'slf self,
        ctxt: CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<dyn Iterator<Item = LocalNode<'tcx>> + 'slf>
    where
        'tcx: 'mir,
    {
        let rp = self.assigned_lifetime_projection(ctxt);
        Box::new(std::iter::once(LocalNode::LifetimeProjection(rp)))
    }
}

impl<'tcx> BorrowEdge<'tcx> {
    pub(crate) fn borrow_index(&self) -> Option<BorrowIndex> {
        self.borrow_index
    }

    pub fn region(&self) -> ty::Region<'tcx> {
        self.region
    }

    pub fn kind(&self) -> mir::BorrowKind {
        self.kind
    }

    pub fn assigned_ref(&self) -> MaybeLabelledPlace<'tcx> {
        self.assigned_ref
    }

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
        };
        borrow.assert_validity(ctxt.bc_ctxt());
        borrow
    }

    pub(crate) fn reserve_location(&self) -> Location {
        self.reserve_location
    }

    pub fn is_mut(&self) -> bool {
        self.kind.mutability() == Mutability::Mut
    }

    /// The deref of the assigned place of the borrow. For example, if the borrow is
    /// `let x = &mut y;`, then the deref place is `*x`.
    pub fn deref_place(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> MaybeLabelledPlace<'tcx> {
        self.assigned_ref.project_deref(ctxt)
    }

    /// The region projection associated with the *type* of the assigned place
    /// of the borrow. For example in `let x: &'x mut i32 = ???`, the assigned
    /// region projection is `x↓'x`.
    pub(crate) fn assigned_lifetime_projection<'a>(
        &self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>
    where
        'tcx: 'a,
    {
        match self.assigned_ref.ty(ctxt).ty.kind() {
            ty::TyKind::Ref(region, _, _) => LifetimeProjection::new(
                self.assigned_ref,
                (*region).into(),
                self.assigned_lifetime_projection_label,
                ctxt.ctxt(),
            )
            .unwrap(),
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
