//! Checks, run under `PCG_VALIDITY_CHECKS`, that the PCG's state and actions
//! follow Rust's rules: each action does exactly what its kind says and
//! changes only what it names ([`action`]), every capability that rises has
//! a source ([`conservation`]), each loan gives back what it took
//! ([`ledger`]), replaying the recorded capability changes reproduces each
//! state ([`replay`]), and each state keeps its invariants ([`state`]). The
//! [`oracle`] compares the states with rustc's facts.
//!
//! A failed check reports `PCG Check Failed: [function] check: message`,
//! where `check` names the rule, and panics unless
//! `PCG_VALIDITY_CHECKS_WARN_ONLY` or `PCG_CHECKS_WARN_ONLY` is set or the
//! failure is one of `PCG_EXPECTED_CHECK_FAILURES`: the test harnesses pass
//! the failures a test file or crate is known to have, and compare the
//! reported lines with them.

pub(crate) mod action;
pub(crate) mod conservation;
pub(crate) mod ledger;
pub mod oracle;
pub(crate) mod replay;
pub(crate) mod state;

use std::{cmp::Ordering, collections::BTreeSet, sync::Mutex};

use crate::{
    action::{CapabilityChanges, PcgAction},
    pcg::{CapabilityKind, place_capabilities::PlaceCapabilities, triple::PlaceCondition},
    utils::{
        CompilerCtxt, DebugCtxt, HasCompilerCtxt, PcgSettings, Place, SETTINGS,
        display::DisplayWithCompilerCtxt,
    },
    validity_checks_warn_only,
};

/// The failures a [`CheckFailureRecorder`] records, while one exists.
static RECORDED: Mutex<Option<BTreeSet<(String, String)>>> = Mutex::new(None);

/// While it exists, the checks that fail are recorded instead of panicking.
/// This is for tests that run the PCG in-process and list the known
/// violations of their code, as test files do with `// PCG_EXPECTED_FAILURE`
/// markers.
pub struct CheckFailureRecorder(());

impl CheckFailureRecorder {
    /// Starts recording.
    #[must_use]
    pub fn start() -> Self {
        *RECORDED.lock().unwrap() = Some(BTreeSet::new());
        Self(())
    }

    /// Stops recording, and returns each failure as the check's name and the
    /// function it failed in.
    #[must_use]
    pub fn finish(self) -> BTreeSet<(String, String)> {
        RECORDED.lock().unwrap().take().unwrap_or_default()
    }
}

impl Drop for CheckFailureRecorder {
    fn drop(&mut self) {
        *RECORDED.lock().unwrap() = None;
    }
}

/// Whether the checks of this module run under `settings`.
pub(crate) fn enabled(settings: &PcgSettings) -> bool {
    settings.validity_checks
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
    let function = ctxt.func_name();
    let message = format!("PCG Check Failed: [{function}] {check}: {message}");
    tracing::error!("{message}");
    let failure = (check.to_owned(), function);
    if let Some(recorded) = RECORDED.lock().unwrap().as_mut() {
        recorded.insert(failure);
        return;
    }
    assert!(
        validity_checks_warn_only()
            || SETTINGS.checks_warn_only
            || SETTINGS.expected_check_failures.contains(&failure),
        "{message}"
    );
}

/// Whether a place that had `old` rises when it gets `new`: it had nothing,
/// or `new` is not at most `old`.
pub(crate) fn rises(old: Option<CapabilityKind>, new: CapabilityKind) -> bool {
    old.is_none_or(|old| {
        !matches!(
            new.partial_cmp(&old),
            Some(Ordering::Less | Ordering::Equal)
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
    let mut changes = CapabilityChanges::default();
    let mut violations = vec![];
    let changed = action::changes(before, after);
    for &action::Change {
        place,
        old,
        new,
        old_record,
        new_record,
    } in &changed
    {
        if old != new {
            changes.set(place, new);
        }
        if place.contains_unsafe_deref(ctxt) {
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
        &changed,
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
