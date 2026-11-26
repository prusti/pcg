//! The per-loan ledger: a mutable loan gives back, when its edge is removed,
//! exactly what it took when it was created, activated or lent at a join
//! (rustc: a loan ends, and the place is accessible as before). It may give
//! back less only if an explicit `WeakenSuspended` lowered what the lender
//! gets back, at a join or a loop head. This is the half of conservation that
//! a source check lacks: a give-back that is lower than the take loses a
//! capability without an action that says so.
//!
//! Loans are identified by their body and the location that creates them, as
//! in rustc's borrow set. The ledger is kept across the iterations of the
//! analysis; the takes of the last iteration count.

use std::{cell::RefCell, collections::HashMap};

use super::{action::Violation, show};
use crate::{
    action::PcgAction,
    borrow_pcg::{action::BorrowPcgActionKind, edge::kind::BorrowPcgEdgeKind},
    pcg::{
        CapabilityKind,
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesReader},
    },
    rustc_interface::{hir::def_id::DefId, middle::mir},
    utils::{CompilerCtxt, PlaceLike, display::DisplayWithCompilerCtxt},
};

/// What a loan took from its lender.
#[derive(Clone, Copy)]
struct Take {
    capability: CapabilityKind,
    lender: mir::Local,
    /// Whether a `WeakenSuspended` of a place of the lender's local may have
    /// lowered what the lender gets back.
    weakened: bool,
}

thread_local! {
    static LEDGER: RefCell<HashMap<(DefId, mir::Location), Take>> = RefCell::new(HashMap::new());
}

/// Starts the ledger of a new body.
pub(crate) fn reset() {
    LEDGER.with(|ledger| ledger.borrow_mut().clear());
}

fn record_take(loan: (DefId, mir::Location), capability: CapabilityKind, lender: mir::Local) {
    LEDGER.with(|ledger| {
        ledger.borrow_mut().insert(
            loan,
            Take {
                capability,
                lender,
                weakened: false,
            },
        );
    });
}

/// Records what `action` takes, and checks what it gives back, given the
/// state `before` and `after` it.
pub(crate) fn observe<'a, 'tcx: 'a>(
    before: &PlaceCapabilities<'tcx>,
    after: &PlaceCapabilities<'tcx>,
    action: &PcgAction<'tcx>,
    ctxt: CompilerCtxt<'a, 'tcx>,
) -> Vec<Violation> {
    let PcgAction::Borrow(action) = action else {
        return vec![];
    };
    let body = ctxt.body().source.def_id();
    let mut violations = vec![];
    match &action.kind {
        BorrowPcgActionKind::AddEdge { edge } => {
            if let BorrowPcgEdgeKind::Borrow(borrow) = edge.kind()
                && matches!(
                    borrow.kind(),
                    mir::BorrowKind::Mut {
                        kind: mir::MutBorrowKind::Default | mir::MutBorrowKind::ClosureCapture
                    }
                )
                && let Some(lender) = borrow.blocked_place.as_current_place()
                && let Some(taken) = before.get(lender, ctxt)
            {
                record_take((body, borrow.reserve_location()), taken, lender.local);
            }
        }
        BorrowPcgActionKind::ActivateTwoPhaseBorrow { borrow } => {
            if let Some(lender) = borrow.blocked_place.as_current_place()
                && let Some(taken) = before.suspended(lender)
            {
                record_take((body, borrow.reserve_location()), taken, lender.local);
            }
        }
        BorrowPcgActionKind::Lend { place, edge } => {
            if let BorrowPcgEdgeKind::Borrow(borrow) = edge.kind()
                && borrow.is_mut()
                && let Some(taken) = after.suspended(*place)
            {
                record_take((body, borrow.reserve_location()), taken, place.local);
            }
        }
        BorrowPcgActionKind::WeakenSuspended { place, .. } => LEDGER.with(|ledger| {
            for take in ledger.borrow_mut().values_mut() {
                if take.lender == place.local {
                    take.weakened = true;
                }
            }
        }),
        BorrowPcgActionKind::RemoveEdge(edge) => {
            let BorrowPcgEdgeKind::Borrow(borrow) = edge.kind() else {
                return violations;
            };
            let Some(lender) = borrow.blocked_place.as_current_place() else {
                return violations;
            };
            let Some(take) = LEDGER.with(|ledger| {
                ledger
                    .borrow()
                    .get(&(body, borrow.reserve_location()))
                    .copied()
            }) else {
                return violations;
            };
            for (place, returned) in after.iter() {
                if !lender.is_prefix_of(place)
                    || place.contains_unsafe_deref(ctxt)
                    || before.get(place, ctxt) == Some(returned)
                {
                    continue;
                }
                let share = lender.share_at(take.capability, place, ctxt);
                if !share.is_some_and(|share| returned <= share) {
                    violations.push(Violation::new(
                        "ledger",
                        format!(
                            "gives {} back to {}, more than the share {} of the {} the loan took from {}",
                            show(Some(returned)),
                            place.display_string(ctxt),
                            show(share),
                            show(Some(take.capability)),
                            lender.display_string(ctxt)
                        ),
                    ));
                } else if place == lender && returned != take.capability && !take.weakened {
                    violations.push(Violation::new(
                        "ledger",
                        format!(
                            "gives {} back to {}, but the loan took {} and nothing weakened it",
                            show(Some(returned)),
                            lender.display_string(ctxt),
                            show(Some(take.capability))
                        ),
                    ));
                }
            }
        }
        _ => {}
    }
    violations
}
