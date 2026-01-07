use derive_more::From;

use super::region_projection::LifetimeProjectionLabel;
use crate::{
    borrow_pcg::{edge::kind::BorrowPcgEdgeType, edge_data::LabelNodePredicate},
    utils::{CompilerCtxt, FilterMutResult, Place, SnapshotLocation},
};

impl std::ops::BitOrAssign for LabelLifetimeProjectionResult {
    fn bitor_assign(&mut self, rhs: Self) {
        if rhs > *self {
            *self = rhs;
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, PartialOrd, Ord)]
pub enum LabelLifetimeProjectionResult {
    Unchanged = 0,
    Changed = 1,
    ShouldCollapse = 2,
}

impl LabelLifetimeProjectionResult {
    pub(crate) fn to_filter_mut_result(self) -> FilterMutResult {
        match self {
            LabelLifetimeProjectionResult::Changed => FilterMutResult::Changed,
            LabelLifetimeProjectionResult::Unchanged => FilterMutResult::Unchanged,
            LabelLifetimeProjectionResult::ShouldCollapse => FilterMutResult::Remove,
        }
    }
}

pub trait LabelLifetimeProjection<'a, 'tcx> {
    fn label_lifetime_projection(
        &mut self,
        predicate: &LabelNodePredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> LabelLifetimeProjectionResult;
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub(crate) enum SourceOrTarget {
    Source,
    Target,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub(crate) struct LabelNodeContext {
    source_or_target: SourceOrTarget,
    edge_type: BorrowPcgEdgeType,
}

impl LabelNodeContext {
    pub(crate) fn new(source_or_target: SourceOrTarget, edge_type: BorrowPcgEdgeType) -> Self {
        Self {
            source_or_target,
            edge_type,
        }
    }

    pub(crate) fn source_or_target(self) -> SourceOrTarget {
        self.source_or_target
    }

    pub(crate) fn edge_type(self) -> BorrowPcgEdgeType {
        self.edge_type
    }
}

pub(crate) trait LabelPlaceWithContext<'tcx, T> {
    fn label_place_with_context(
        &mut self,
        predicate: &LabelNodePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        label_context: T,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool;
}

impl<'tcx, T: LabelPlace<'tcx>, U> LabelPlaceWithContext<'tcx, U> for T {
    fn label_place_with_context(
        &mut self,
        predicate: &LabelNodePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        _label_context: U,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.label_place(predicate, labeller, ctxt)
    }
}

pub(crate) trait LabelPlace<'tcx> {
    fn label_place(
        &mut self,
        predicate: &LabelNodePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool;
}

pub trait PlaceLabeller<'tcx> {
    fn place_label(&self, place: Place<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> SnapshotLocation;
}

#[derive(From)]
pub(crate) struct SetLabel(pub(crate) SnapshotLocation);

impl<'tcx> PlaceLabeller<'tcx> for SetLabel {
    fn place_label(&self, _place: Place<'tcx>, _ctxt: CompilerCtxt<'_, 'tcx>) -> SnapshotLocation {
        self.0
    }
}
