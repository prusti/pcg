use tracing::instrument;

use super::borrow_pcg_edge::BorrowPcgEdge;
use super::edge::kind::BorrowPcgEdgeKind;
use super::state::BorrowsState;
use crate::action::BorrowPcgAction;
use crate::borrow_checker::BorrowCheckerInterface;
use crate::borrow_pcg::borrow_pcg_edge::LocalNode;
use crate::borrow_pcg::graph::BorrowsGraph;
use crate::borrow_pcg::has_pcs_elem::LabelRegionProjection;
use crate::borrow_pcg::region_projection::{RegionProjection, RegionProjectionLabel};
use crate::free_pcs::CapabilityKind;
use crate::pcg::place_capabilities::PlaceCapabilities;
use crate::pcg::PcgError;
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::maybe_old::MaybeOldPlace;
use crate::utils::{CompilerCtxt, HasPlace, Place, SnapshotLocation};
use crate::{RestoreCapability, Weaken};

pub mod actions;

impl<'tcx> BorrowPcgAction<'tcx> {
    pub(crate) fn restore_capability(
        place: Place<'tcx>,
        capability: CapabilityKind,
        debug_context: impl Into<String>,
    ) -> Self {
        BorrowPcgAction {
            kind: BorrowPcgActionKind::Restore(RestoreCapability::new(place, capability)),
            debug_context: Some(debug_context.into()),
        }
    }

    pub(crate) fn weaken(
        place: Place<'tcx>,
        from: CapabilityKind,
        to: Option<CapabilityKind>,
    ) -> Self {
        BorrowPcgAction {
            kind: BorrowPcgActionKind::Weaken(Weaken::new(place, from, to)),
            debug_context: None,
        }
    }

    pub(crate) fn set_latest(
        place: Place<'tcx>,
        location: SnapshotLocation,
        context: impl Into<String>,
    ) -> Self {
        BorrowPcgAction {
            kind: BorrowPcgActionKind::SetLatest(place, location),
            debug_context: Some(context.into()),
        }
    }

    pub(crate) fn remove_edge(edge: BorrowPcgEdge<'tcx>, context: impl Into<String>) -> Self {
        BorrowPcgAction {
            kind: BorrowPcgActionKind::RemoveEdge(edge),
            debug_context: Some(context.into()),
        }
    }

    pub(crate) fn redirect_edge(
        edge: BorrowPcgEdgeKind<'tcx>,
        from: LocalNode<'tcx>,
        to: LocalNode<'tcx>,
        context: impl Into<String>,
    ) -> Self {
        BorrowPcgAction {
            kind: BorrowPcgActionKind::RedirectEdge { edge, from, to },
            debug_context: Some(context.into()),
        }
    }

    pub(crate) fn add_edge(
        edge: BorrowPcgEdge<'tcx>,
        context: impl Into<String>,
        for_read: bool,
    ) -> Self {
        BorrowPcgAction {
            kind: BorrowPcgActionKind::AddEdge { edge, for_read },
            debug_context: Some(context.into()),
        }
    }

    pub(crate) fn remove_region_projection_label(
        projection: RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        context: impl Into<String>,
    ) -> Self {
        BorrowPcgAction {
            kind: BorrowPcgActionKind::LabelRegionProjection(projection, None),
            debug_context: Some(context.into()),
        }
    }

    pub(crate) fn label_region_projection(
        projection: RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        label: Option<RegionProjectionLabel>,
        context: impl Into<String>,
    ) -> Self {
        BorrowPcgAction {
            kind: BorrowPcgActionKind::LabelRegionProjection(projection, label),
            debug_context: Some(context.into()),
        }
    }

    pub(crate) fn make_place_old(place: Place<'tcx>, reason: MakePlaceOldReason) -> Self {
        BorrowPcgAction {
            kind: BorrowPcgActionKind::MakePlaceOld(place, reason),
            debug_context: None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MakePlaceOldReason {
    StorageDead,
    ReAssign,
    MoveOut,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BorrowPcgActionKind<'tcx> {
    RedirectEdge {
        edge: BorrowPcgEdgeKind<'tcx>,
        from: LocalNode<'tcx>,
        to: LocalNode<'tcx>,
    },
    LabelRegionProjection(
        RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        Option<RegionProjectionLabel>,
    ),
    Weaken(Weaken<'tcx>),
    Restore(RestoreCapability<'tcx>),
    MakePlaceOld(Place<'tcx>, MakePlaceOldReason),
    SetLatest(Place<'tcx>, SnapshotLocation),
    RemoveEdge(BorrowPcgEdge<'tcx>),
    AddEdge {
        edge: BorrowPcgEdge<'tcx>,
        for_read: bool,
    },
}

impl<'tcx, 'a> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for BorrowPcgActionKind<'tcx>
{
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        match self {
            BorrowPcgActionKind::RedirectEdge { edge, from, to } => {
                format!(
                    "Redirect Edge: {} from {} to {}",
                    edge.to_short_string(ctxt),
                    from.to_short_string(ctxt),
                    to.to_short_string(ctxt)
                )
            }
            BorrowPcgActionKind::LabelRegionProjection(rp, label) => {
                format!(
                    "Label Region Projection: {} with {:?}",
                    rp.to_short_string(ctxt),
                    label
                )
            }
            BorrowPcgActionKind::Weaken(weaken) => weaken.debug_line(ctxt),
            BorrowPcgActionKind::Restore(restore_capability) => restore_capability.debug_line(ctxt),
            BorrowPcgActionKind::MakePlaceOld(place, reason) => {
                format!(
                    "Make {} an old place ({:?})",
                    place.to_short_string(ctxt),
                    reason
                )
            }
            BorrowPcgActionKind::SetLatest(place, location) => format!(
                "Set Latest of {} to {:?}",
                place.to_short_string(ctxt),
                location
            ),
            BorrowPcgActionKind::RemoveEdge(borrow_pcgedge) => {
                format!("Remove Edge {}", borrow_pcgedge.to_short_string(ctxt))
            }
            BorrowPcgActionKind::AddEdge { edge, for_read } => format!(
                "Add Edge: {}; for read: {}",
                edge.to_short_string(ctxt),
                for_read
            ),
        }
    }
}

impl<'tcx> BorrowsGraph<'tcx> {
    #[must_use]
    fn redirect_edge(
        &mut self,
        mut edge: BorrowPcgEdgeKind<'tcx>,
        from: LocalNode<'tcx>,
        to: LocalNode<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let conditions = self.remove(&edge).unwrap();
        if edge.redirect(from, to, ctxt) {
            self.insert(BorrowPcgEdge::new(edge, conditions), ctxt);
        }
        true
    }
}

impl<'tcx> BorrowsState<'tcx> {
    #[instrument(skip(self, action, capabilities, ctxt))]
    pub(crate) fn apply_action(
        &mut self,
        action: BorrowPcgAction<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        let result = match action.kind {
            BorrowPcgActionKind::RedirectEdge { edge, from, to } => {
                self.graph.redirect_edge(edge, from, to, ctxt)
            }
            BorrowPcgActionKind::Restore(restore) => {
                let restore_place = restore.place();
                if let Some(cap) = capabilities.get(restore_place) {
                    assert!(cap < restore.capability(), "Current capability {:?} is not less than the capability to restore to {:?}", cap, restore.capability());
                }
                if !capabilities.insert(restore_place, restore.capability()) {
                    panic!("Capability should have been updated")
                }
                true
            }
            BorrowPcgActionKind::Weaken(weaken) => {
                let weaken_place = weaken.place();
                assert_eq!(capabilities.get(weaken_place), Some(weaken.from));
                match weaken.to {
                    Some(to) => assert!(capabilities.insert(weaken_place, to)),
                    None => assert!(capabilities.remove(weaken_place).is_some()),
                }
                true
            }
            BorrowPcgActionKind::MakePlaceOld(place, _) => self.make_place_old(place, ctxt),
            BorrowPcgActionKind::SetLatest(place, location) => self.set_latest(place, location),
            BorrowPcgActionKind::RemoveEdge(edge) => self.remove(&edge, capabilities, ctxt),
            BorrowPcgActionKind::AddEdge { edge, for_read } => {
                self.handle_add_edge(edge, for_read, capabilities, ctxt)?
            }
            BorrowPcgActionKind::LabelRegionProjection(rp, label) => {
                self.label_region_projection(&rp, label, ctxt)
            }
        };
        Ok(result)
    }

    fn make_place_old(&mut self, place: Place<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.graph.make_place_old(place, &self.latest, ctxt)
    }

    fn label_region_projection(
        &mut self,
        projection: &RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        label: Option<RegionProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.graph
            .mut_edges(|edge| edge.label_region_projection(projection, label, ctxt))
    }

    #[instrument(skip(self, edge, capabilities, ctxt), fields(edge = edge.to_short_string(ctxt)))]
    fn handle_add_edge(
        &mut self,
        edge: BorrowPcgEdge<'tcx>,
        for_read: bool,
        capabilities: &mut PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        let mut changed = self.insert(edge.clone(), ctxt);
        Ok(match edge.kind {
            BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) => {
                // We only want to change capability for expanding x -> *x, not
                // for expanding region projections
                if changed && expansion.base.is_place() {
                    let base = expansion.base;
                    let base_capability = capabilities.get(base.place());
                    let expanded_capability = if for_read {
                        CapabilityKind::Read
                    } else if let Some(capability) = base_capability {
                        capability
                    } else {
                        // TODO
                        // pcg_validity_assert!(
                        //     false,
                        //     "Base capability for {} is not set",
                        //     base.place().to_short_string(ctxt)
                        // );
                        return Ok(true);
                        // panic!("Base capability should be set");
                    };

                    if for_read {
                        changed |= capabilities.insert(base.place(), CapabilityKind::Read);
                    } else {
                        changed |= capabilities.remove(base.place()).is_some();
                    }

                    for p in expansion.expansion.iter() {
                        if !p.place().is_owned(ctxt) {
                            tracing::debug!(
                                "Inserting capability {:?} for {}",
                                expanded_capability,
                                p.place().to_short_string(ctxt)
                            );
                            changed |=
                                capabilities.insert(p.place(), expanded_capability);
                        }
                    }
                }
                changed
            }
            _ => changed,
        })
    }

    #[must_use]
    fn set_latest<T: Into<SnapshotLocation>>(&mut self, place: Place<'tcx>, location: T) -> bool {
        let location = location.into();
        self.latest.insert(place, location)
    }
}
