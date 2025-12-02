//! Borrow edges
use crate::{
    borrow_pcg::{
        edge_data::{LabelEdgePlaces, LabelPlacePredicate, edgedata_enum},
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
        HasBorrowCheckerCtxt, HasCompilerCtxt, HasPlace,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        remote::RemotePlace,
    },
};

use crate::{
    borrow_pcg::{
        borrow_pcg_edge::{BlockedNode, LocalNode},
        edge_data::EdgeData,
        region_projection::LifetimeProjection,
    },
    utils::{
        CompilerCtxt,
        place::{maybe_old::MaybeLabelledPlace, maybe_remote::MaybeRemotePlace},
        validity::HasValidityCheck,
    },
};

/// A borrow that is explicit in the MIR (e.g. `let x = &mut y;`)
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct LocalBorrow<'tcx> {
    /// The place that is blocked by the borrow, e.g. the y in `let x = &mut y;`
    pub blocked_place: MaybeLabelledPlace<'tcx>,
    /// The place that is assigned by the borrow, e.g. the x in `let x = &mut y;`
    pub(crate) assigned_ref: MaybeLabelledPlace<'tcx>,
    kind: mir::BorrowKind,

    /// The location when the borrow was created
    reserve_location: Location,

    pub region: ty::Region<'tcx>,

    // For some reason this may not be defined for certain shared borrows
    borrow_index: Option<BorrowIndex>,

    assigned_lifetime_projection_label: Option<LifetimeProjectionLabel>,
}

impl<'a, 'tcx> LabelLifetimeProjection<'a, 'tcx> for LocalBorrow<'tcx> {
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

impl<'tcx> LabelEdgePlaces<'tcx> for LocalBorrow<'tcx> {
    fn label_blocked_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.blocked_place.label_place_with_context(
            predicate,
            labeller,
            LabelNodeContext::Other,
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
            LabelNodeContext::Other,
            ctxt,
        )
    }
}

/// An (implied) borrow that connects a remote place to a reference-typed
/// function input. Intuitively, the blocked place is not accessible to the
/// function.
#[derive(Copy, PartialEq, Eq, Clone, Debug, Hash)]
pub struct RemoteBorrow<'tcx> {
    local: mir::Local,

    // We don't assume that it's still the dereference of the local of the remote place,
    // because that local could be moved and the assigned ref should be renamed accordingly.
    assigned_ref: MaybeLabelledPlace<'tcx>,

    rp_snapshot_location: Option<LifetimeProjectionLabel>,
}

impl<'a, 'tcx> LabelLifetimeProjection<'a, 'tcx> for RemoteBorrow<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        predicate: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        if predicate.matches(self.assigned_lifetime_projection(ctxt).rebase(), ctxt) {
            self.rp_snapshot_location = label;
            LabelLifetimeProjectionResult::Changed
        } else {
            LabelLifetimeProjectionResult::Unchanged
        }
    }
}

impl<'tcx> LabelEdgePlaces<'tcx> for RemoteBorrow<'tcx> {
    fn label_blocked_places(
        &mut self,
        _predicate: &LabelPlacePredicate<'tcx>,
        _labeller: &impl PlaceLabeller<'tcx>,
        _ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        false
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.assigned_ref.label_place_with_context(
            predicate,
            labeller,
            LabelNodeContext::Other,
            ctxt,
        )
    }
}

impl<'tcx> RemoteBorrow<'tcx> {
    pub(crate) fn deref_place(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> MaybeLabelledPlace<'tcx> {
        self.assigned_ref.project_deref(ctxt)
    }

    pub(crate) fn blocked_place(&self) -> RemotePlace {
        RemotePlace::new(self.local)
    }

    pub(crate) fn assigned_ref(&self) -> MaybeLabelledPlace<'tcx> {
        self.assigned_ref
    }

    pub(crate) fn assigned_lifetime_projection<'a>(
        &self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>
    where
        'tcx: 'a,
    {
        let rp = self.assigned_ref.base_lifetime_projection(ctxt).unwrap();
        if let Some(location) = self.rp_snapshot_location {
            rp.with_label(Some(location), ctxt)
        } else {
            rp
        }
    }

    pub(crate) fn is_mut(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.assigned_ref.place().is_mut_ref(ctxt)
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for RemoteBorrow<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(
            format!(
                "{} -> {}",
                self.blocked_place().display_string(ctxt),
                self.assigned_lifetime_projection(ctxt).display_string(ctxt)
            )
            .into(),
        )
    }
}

impl<'tcx> HasValidityCheck<'_, 'tcx> for RemoteBorrow<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.local.check_validity(ctxt)?;
        self.assigned_ref.check_validity(ctxt)
    }
}

impl<'tcx> EdgeData<'tcx> for RemoteBorrow<'tcx> {
    fn blocks_node<'slf>(&self, node: BlockedNode<'tcx>, _ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        if let BlockedNode::Place(MaybeRemotePlace::Remote(rp)) = node {
            self.blocked_place() == rp
        } else {
            false
        }
    }

    fn blocked_nodes<'slf, BC: Copy>(
        &'slf self,
        _ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn Iterator<Item = PcgNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(std::iter::once(self.blocked_place().into()))
    }

    fn blocked_by_nodes<'slf, 'mir: 'slf, BC: Copy>(
        &'slf self,
        ctxt: CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<dyn Iterator<Item = LocalNode<'tcx>> + 'slf>
    where
        'tcx: 'mir,
    {
        Box::new(std::iter::once(
            self.assigned_lifetime_projection(ctxt).into(),
        ))
    }
}

impl RemoteBorrow<'_> {
    pub(crate) fn new(local: mir::Local) -> Self {
        Self {
            local,
            assigned_ref: local.into(),
            rp_snapshot_location: None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BorrowEdge<'tcx> {
    Local(LocalBorrow<'tcx>),
    Remote(RemoteBorrow<'tcx>),
}

edgedata_enum!(
    BorrowEdge<'tcx>,
    Local(LocalBorrow<'tcx>),
    Remote(RemoteBorrow<'tcx>),
);

impl<'tcx> BorrowEdge<'tcx> {
    pub(crate) fn borrow_index(&self) -> Option<BorrowIndex> {
        match self {
            BorrowEdge::Local(borrow) => borrow.borrow_index,
            BorrowEdge::Remote(_) => None,
        }
    }

    pub fn kind(&self) -> Option<mir::BorrowKind> {
        match self {
            BorrowEdge::Local(borrow) => Some(borrow.kind),
            BorrowEdge::Remote(_) => None,
        }
    }

    pub fn is_mut(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        match self {
            BorrowEdge::Local(borrow) => borrow.is_mut(),
            BorrowEdge::Remote(borrow) => borrow.is_mut(ctxt),
        }
    }

    pub(crate) fn reserve_location(&self) -> Option<Location> {
        match self {
            BorrowEdge::Local(borrow) => Some(borrow.reserve_location()),
            BorrowEdge::Remote(_) => None,
        }
    }

    pub fn borrow_region(&self) -> Option<ty::Region<'tcx>> {
        match self {
            BorrowEdge::Local(borrow) => Some(borrow.region),
            BorrowEdge::Remote(_) => None,
        }
    }

    pub(crate) fn assigned_lifetime_projection<'a>(
        &self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>
    where
        'tcx: 'a,
    {
        match self {
            BorrowEdge::Local(borrow) => borrow.assigned_lifetime_projection(ctxt),
            BorrowEdge::Remote(borrow) => borrow.assigned_lifetime_projection(ctxt),
        }
    }

    pub fn blocked_place(&self) -> MaybeRemotePlace<'tcx> {
        match self {
            BorrowEdge::Local(borrow) => borrow.blocked_place.into(),
            BorrowEdge::Remote(borrow) => borrow.blocked_place().into(),
        }
    }

    pub fn deref_place(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> MaybeLabelledPlace<'tcx> {
        match self {
            BorrowEdge::Local(borrow) => borrow.deref_place(ctxt),
            BorrowEdge::Remote(borrow) => borrow.deref_place(ctxt),
        }
    }

    pub fn assigned_ref(&self) -> MaybeLabelledPlace<'tcx> {
        match self {
            BorrowEdge::Local(borrow) => borrow.assigned_ref,
            BorrowEdge::Remote(remote) => remote.assigned_ref(),
        }
    }
}
impl<'tcx> HasValidityCheck<'_, 'tcx> for LocalBorrow<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.blocked_place.check_validity(ctxt)?;
        self.assigned_ref.check_validity(ctxt)?;
        Ok(())
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt> for LocalBorrow<'tcx> {
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

impl<'tcx> EdgeData<'tcx> for LocalBorrow<'tcx> {
    fn blocks_node<'slf>(&self, node: BlockedNode<'tcx>, _ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        match node {
            PcgNode::Place(MaybeRemotePlace::Local(p)) => self.blocked_place == p,
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

impl<'tcx> LocalBorrow<'tcx> {
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
            "reborrow blocking {} assigned to {}",
            self.blocked_place(),
            self.assigned_ref()
        )
    }
}
