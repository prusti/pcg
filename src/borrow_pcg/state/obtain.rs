use crate::borrow_pcg::action::executed_actions::ExecutedActions;
use crate::borrow_pcg::action::BorrowPCGAction;
use crate::borrow_pcg::borrow_pcg_edge::{BorrowPCGEdge, LocalNode};
use crate::borrow_pcg::borrow_pcg_expansion::{BorrowPCGExpansion, PlaceExpansion};
use crate::borrow_pcg::edge::kind::BorrowPCGEdgeKind;
use crate::borrow_pcg::edge_data::EdgeData;
use crate::borrow_pcg::path_condition::PathConditions;
use crate::borrow_pcg::region_projection::RegionProjection;
use crate::borrow_pcg::state::BorrowsState;
use crate::free_pcs::CapabilityKind;
use crate::pcg::place_capabilities::PlaceCapabilities;
use crate::pcg::PcgError;
use crate::rustc_interface::middle::mir::{BorrowKind, Location, MutBorrowKind};
use crate::rustc_interface::middle::ty::Mutability;
use crate::utils::maybe_old::MaybeOldPlace;
use crate::utils::{CompilerCtxt, HasPlace, Place, ShallowExpansion, SnapshotLocation};

impl ObtainReason {
    /// After calling `obtain` for a place, the minimum capability that we
    /// expect the place to have.
    pub(crate) fn min_post_obtain_capability(&self) -> CapabilityKind {
        match self {
            ObtainReason::MoveOperand => CapabilityKind::Exclusive,
            ObtainReason::CopyOperand => CapabilityKind::Read,
            ObtainReason::FakeRead => CapabilityKind::Read,
            ObtainReason::AssignTarget => CapabilityKind::Write,
            ObtainReason::CreateReference(borrow_kind) => match borrow_kind {
                BorrowKind::Shared => CapabilityKind::Read,
                BorrowKind::Fake(_) => unreachable!(),
                BorrowKind::Mut { kind } => match kind {
                    MutBorrowKind::Default => CapabilityKind::Exclusive,
                    MutBorrowKind::TwoPhaseBorrow => CapabilityKind::Read,
                    MutBorrowKind::ClosureCapture => CapabilityKind::Exclusive,
                },
            },
            ObtainReason::CreatePtr(mutability) => {
                if mutability.is_mut() {
                    CapabilityKind::Exclusive
                } else {
                    CapabilityKind::Read
                }
            }
            ObtainReason::RValueSimpleRead => CapabilityKind::Read,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum ObtainReason {
    MoveOperand,
    CopyOperand,
    FakeRead,
    AssignTarget,
    CreateReference(BorrowKind),
    CreatePtr(Mutability),
    /// Just to read the place, but not refer to it
    RValueSimpleRead,
}

impl<'tcx> BorrowsState<'tcx> {



    #[allow(clippy::too_many_arguments)]
    fn expand_place_one_level(
        &mut self,
        base: Place<'tcx>,
        expansion: &ShallowExpansion<'tcx>,
        location: Location,
        for_exclusive: bool,
        actions: &mut ExecutedActions<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        let target = expansion.target_place;

        // We don't introduce an expansion if the place is owned, because
        // that is handled by the owned PCG.
        if !target.is_owned(ctxt) {
            let place_expansion = PlaceExpansion::from_places(expansion.expansion().clone(), ctxt);
            let expansion: BorrowPCGExpansion<'tcx, LocalNode<'tcx>> = BorrowPCGExpansion::new(
                base.into(),
                place_expansion,
                location,
                for_exclusive,
                ctxt,
            )?;

            if expansion
                .blocked_by_nodes(ctxt)
                .iter()
                .all(|node| self.contains(*node, ctxt))
            {
                return Ok(false);
            }

            if base.is_mut_ref(ctxt)
                && base.contains_mutable_region_projections(ctxt)
                && for_exclusive
            {
                let place: MaybeOldPlace<'tcx> = base.into();
                self.label_region_projection(
                    &place.base_region_projection(ctxt).unwrap(),
                    Some(location.into()),
                    ctxt,
                );
            }

            let action = BorrowPCGAction::add_edge(
                BorrowPCGEdge::new(
                    BorrowPCGEdgeKind::BorrowPCGExpansion(expansion),
                    PathConditions::new(location.block),
                ),
                for_exclusive,
            );
            self.record_and_apply_action(action, actions, capabilities, ctxt)?;
        }
        Ok(true)
    }

    /// Inserts edges to ensure that the borrow PCG is expanded to at least
    /// `to_place`. We assume that any unblock operations have already been
    /// performed.
    pub(crate) fn expand_to(
        &mut self,
        to_place: Place<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
        obtain_reason: ObtainReason,
        location: Location,
    ) -> Result<ExecutedActions<'tcx>, PcgError> {
        tracing::debug!("Expanding to {:?}", to_place);
        let for_exclusive = obtain_reason.min_post_obtain_capability() != CapabilityKind::Read;
        let mut actions = ExecutedActions::new();

        for (base, _) in to_place.iter_projections(ctxt) {
            let base = base.with_inherent_region(ctxt);
            let expansion = base.expand_one_level(to_place, ctxt)?;
            if self.expand_place_one_level(
                base,
                &expansion,
                location,
                for_exclusive,
                &mut actions,
                capabilities,
                ctxt,
            )? {
                for rp in base.region_projections(ctxt) {
                    let dest_places = expansion
                        .expansion()
                        .iter()
                        .filter(|e| {
                            e.region_projections(ctxt)
                                .into_iter()
                                .any(|child_rp| rp.region(ctxt) == child_rp.region(ctxt))
                        })
                        .copied()
                        .collect::<Vec<_>>();
                    if !dest_places.is_empty() {
                        let rp: RegionProjection<'tcx, MaybeOldPlace<'tcx>> = rp.into();
                        let place_expansion = PlaceExpansion::from_places(dest_places, ctxt);
                        let expansion = BorrowPCGExpansion::new(
                            rp.into(),
                            place_expansion,
                            location,
                            for_exclusive,
                            ctxt,
                        )?;
                        self.record_and_apply_action(
                            BorrowPCGAction::add_edge(
                                BorrowPCGEdge::new(
                                    BorrowPCGEdgeKind::BorrowPCGExpansion(expansion),
                                    PathConditions::new(location.block),
                                ),
                                for_exclusive,
                            ),
                            &mut actions,
                            capabilities,
                            ctxt,
                        )?;
                        if base.is_mut_ref(ctxt) && for_exclusive {
                            self.label_region_projection(
                                &rp,
                                Some(SnapshotLocation::before(location).into()),
                                ctxt,
                            );
                        }
                    }
                }
            }
        }

        Ok(actions)
    }
}
