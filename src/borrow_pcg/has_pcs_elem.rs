use derive_more::From;

use super::region_projection::LifetimeProjectionLabel;
use crate::{
    borrow_pcg::edge::kind::BorrowPcgEdgeType,
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

/// Analogous to `LabelPlace` for places.
pub trait LabelLifetimeProjection<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        label: Option<LifetimeProjectionLabel>,
    ) -> LabelLifetimeProjectionResult;
}

macro_rules! label_lifetime_projection_wrapper {
    ($ty:ty) => {
        impl<'tcx, P> LabelLifetimeProjection<'tcx> for $ty
        where
            <Self as std::ops::Deref>::Target: LabelLifetimeProjection<'tcx>,
        {
            fn label_lifetime_projection(
                &mut self,
                label: Option<LifetimeProjectionLabel>,
            ) -> LabelLifetimeProjectionResult {
                use std::ops::DerefMut;
                self.deref_mut().label_lifetime_projection(label)
            }
        }
    };
}

pub(crate) use label_lifetime_projection_wrapper;

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

pub(crate) trait LabelPlace<'tcx, Ctxt, P = Place<'tcx>> {
    fn label_place(&mut self, labeller: &impl PlaceLabeller<'tcx, Ctxt, P>, ctxt: Ctxt) -> bool;
}

macro_rules! label_place_wrapper {
    ($ty:ty) => {
        impl<'tcx, Ctxt, P> LabelPlace<'tcx, Ctxt, P> for $ty
        where
            <Self as std::ops::Deref>::Target: LabelPlace<'tcx, Ctxt, P>,
        {
            fn label_place(
                &mut self,
                labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
                ctxt: Ctxt,
            ) -> bool {
                use std::ops::DerefMut;
                self.deref_mut().label_place(labeller, ctxt)
            }
        }
    };
}

pub(crate) use label_place_wrapper;

pub trait PlaceLabeller<'tcx, Ctxt, P = Place<'tcx>> {
    fn place_label(&self, place: P, ctxt: Ctxt) -> SnapshotLocation;
}

#[derive(From)]
pub(crate) struct SetLabel(pub(crate) SnapshotLocation);

impl<'tcx, Ctxt, P> PlaceLabeller<'tcx, Ctxt, P> for SetLabel {
    fn place_label(&self, _place: P, _ctxt: Ctxt) -> SnapshotLocation {
        self.0
    }
}
