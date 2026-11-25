//! Checks, run under `PCG_VALIDITY_CHECKS`, that the PCG's state and actions
//! follow Rust's rules: each action does exactly what its kind says and
//! changes only what it names ([`action`]), every capability that rises has
//! a source ([`conservation`]), each loan gives back what it took
//! ([`ledger`]), and replaying the recorded actions reproduces each state
//! ([`replay`]).
//!
//! A failed check reports `PCG Check Failed: [function] check: message`,
//! where `check` names the rule, and panics unless
//! `PCG_VALIDITY_CHECKS_WARN_ONLY` is set. The test harness reads these
//! lines to compare them with the failures a test file expects.

pub(crate) mod action;
pub(crate) mod conservation;
pub(crate) mod ledger;
pub(crate) mod replay;
pub(crate) mod state;

use crate::{
    action::{CapabilityChanges, PcgAction},
    pcg::{CapabilityKind, place_capabilities::PlaceCapabilities, triple::PlaceCondition},
    utils::{CompilerCtxt, DebugCtxt, HasCompilerCtxt, Place, display::DisplayWithCompilerCtxt},
    validity_checks_enabled, validity_checks_warn_only,
};

/// Whether the checks of this module run.
pub(crate) fn enabled() -> bool {
    validity_checks_enabled()
}

/// The capability changes `action` lists.
pub(crate) fn listed_changes<'s, 'tcx>(
    action: &'s PcgAction<'tcx>,
) -> &'s CapabilityChanges<Place<'tcx>> {
    match action {
        PcgAction::Borrow(action) => action.capabilities(),
        PcgAction::Owned(action) => action.capabilities(),
    }
}

/// Reports that `check` failed in the function of `ctxt`.
pub(crate) fn fail(ctxt: impl DebugCtxt, check: &str, message: &str) {
    let message = format!(
        "PCG Check Failed: [{}] {check}: {message}",
        ctxt.func_name()
    );
    tracing::error!("{message}");
    assert!(validity_checks_warn_only(), "{message}");
}

/// Whether a place that had `old` rises when it gets `new`: it had nothing,
/// or `new` is not at most `old`.
pub(crate) fn rises(old: Option<CapabilityKind>, new: CapabilityKind) -> bool {
    old.is_none_or(|old| {
        !matches!(
            new.partial_cmp(&old),
            Some(std::cmp::Ordering::Less | std::cmp::Ordering::Equal)
        )
    })
}

/// Checks the effect of a statement's post-condition `post`, which turned
/// `before` into `after`, and returns its capability changes. A statement
/// sets the capability of the place it names (an assignment gives E, a
/// `StorageLive` W, a `StorageDead` removes the local) and ends the loans of
/// the value it overwrites: it drops records of that place's parts. It
/// changes nothing else; any other change is an action of its own.
pub(crate) fn statement_effect<'a, 'tcx: 'a>(
    post: Option<PlaceCondition<'tcx>>,
    before: &PlaceCapabilities<'tcx>,
    after: &PlaceCapabilities<'tcx>,
    ctxt: CompilerCtxt<'a, 'tcx>,
) -> CapabilityChanges<Place<'tcx>> {
    use crate::pcg::place_capabilities::PlaceCapabilitiesReader;
    let mut changes = CapabilityChanges::default();
    let mut violations = vec![];
    let places = before
        .map
        .keys()
        .chain(before.suspended.keys())
        .chain(after.map.keys())
        .chain(after.suspended.keys())
        .copied()
        .collect::<std::collections::HashSet<_>>();
    for place in places {
        let (old, new) = (before.get(place, ctxt), after.get(place, ctxt));
        let (old_record, new_record) = (before.suspended(place), after.suspended(place));
        if old != new {
            changes.set(place, new);
        }
        if place.contains_unsafe_deref(ctxt) || (old == new && old_record == new_record) {
            continue;
        }
        let allowed = match post {
            Some(
                PlaceCondition::Capability(target, _)
                | PlaceCondition::ExpandTwoPhase(target)
                | PlaceCondition::Freeze(target),
            ) => {
                (old == new || place == target)
                    && (old_record == new_record
                        || (new_record.is_none() && target.is_prefix_of(place)))
            }
            Some(PlaceCondition::AllocateOrDeallocate(local) | PlaceCondition::Unalloc(local)) => {
                place.local == local
            }
            Some(PlaceCondition::Return) | None => false,
        };
        if !allowed {
            violations.push(format!(
                "{} goes from {}/record {} to {}/record {}",
                place.display_string(ctxt),
                show(old),
                show(old_record),
                show(new),
                show(new_record)
            ));
        }
    }
    violations.sort();
    for violation in violations {
        fail(
            ctxt,
            "statement-effect",
            &format!("post-condition {post:?}: {violation}"),
        );
    }
    for violation in conservation::check(
        before,
        after,
        conservation::Allowed::post_condition(post),
        ctxt,
    ) {
        fail(
            ctxt,
            violation.check,
            &format!("post-condition {post:?}: {}", violation.message),
        );
    }
    changes
}

/// Shows the capabilities and records of `capabilities` that `filter`
/// selects, sorted, for a failure message.
pub(crate) fn show_state<'a, 'tcx: 'a>(
    capabilities: &PlaceCapabilities<'tcx>,
    filter: impl Fn(Place<'tcx>) -> bool,
    ctxt: impl HasCompilerCtxt<'a, 'tcx>,
) -> String {
    use crate::pcg::place_capabilities::PlaceCapabilitiesReader;
    let mut entries = capabilities
        .iter()
        .filter(|(p, _)| filter(*p))
        .map(|(p, c)| format!("{}: {}", p.display_string(ctxt), show(Some(c))))
        .chain(
            capabilities
                .iter_suspended()
                .filter(|(p, _)| filter(*p))
                .map(|(p, c)| format!("{}: record {}", p.display_string(ctxt), show(Some(c)))),
        )
        .collect::<Vec<_>>();
    entries.sort();
    entries.join(", ")
}

/// A capability as the annotations of test files write it.
pub(crate) fn show(capability: Option<CapabilityKind>) -> &'static str {
    match capability {
        None => "none",
        Some(CapabilityKind::Exclusive) => "E",
        Some(CapabilityKind::ShallowExclusive) => "e",
        Some(CapabilityKind::Read) => "R",
        Some(CapabilityKind::Write) => "W",
    }
}
