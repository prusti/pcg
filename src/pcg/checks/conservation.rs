//! Conservation (principle 4): every rise of a place's capability or record
//! in a step of the analysis has a source that the step may take it from, in
//! the state before the step. Each source corresponds to a Rust event: a loan
//! ending gives back what it took, an unpacking passes on a share of its
//! base, a pack gives the meet of the parts, an assignment or `StorageLive`
//! creates a fresh capability at its place.
//!
//! A rise is a capability or record that the place did not have before and
//! that is not below what it had. The sources are:
//! - `OWN_CAP`, `OWN_REC`: what the place itself held or recorded;
//! - `ANC_CAP`, `ANC_REC`: the share of an ancestor's capability or record
//!   ([`PlaceLike::share_at`]), as unpacking gives it;
//! - `DESC_CAP`: what the place and its parts held, packed together
//!   ([`packed`]); a part that is lent (it records something and holds
//!   nothing) keeps the place from being packed;
//! - `DESC_REC`: what the place and its parts record or, recording nothing,
//!   hold, packed together; a read copy counts through its frozen place;
//! - a fresh capability that a statement's post-condition creates at its
//!   place.
//!
//! R is covered by e at a place when nothing in the place's value is lent or
//! uninitialised: e makes the place's own storage exclusive, and what lies
//! behind its references is held separately (the inverse of unpacking a
//! mutable reference for read, which gives both R).
//!
//! A capability above R that comes from a record consumes it: afterwards no
//! record of the place or of an ancestor covers it.

use super::{
    action::{Change, Violation},
    rises, show,
};
use crate::{
    action::PcgAction,
    borrow_pcg::{action::BorrowPcgActionKind, state::packed},
    owned_pcg::RepackOp,
    pcg::{
        CapabilityKind,
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesReader},
        triple::PlaceCondition,
    },
    utils::{CompilerCtxt, Place, PlaceLike, display::DisplayWithCompilerCtxt},
};

#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub(crate) struct Sources(u8);

impl Sources {
    pub(crate) const NONE: Sources = Sources(0);
    pub(crate) const OWN_CAP: Sources = Sources(1);
    pub(crate) const OWN_REC: Sources = Sources(2);
    pub(crate) const ANC_CAP: Sources = Sources(4);
    pub(crate) const ANC_REC: Sources = Sources(8);
    pub(crate) const DESC_CAP: Sources = Sources(16);
    pub(crate) const DESC_REC: Sources = Sources(32);

    #[must_use]
    pub(crate) const fn or(self, other: Sources) -> Sources {
        Sources(self.0 | other.0)
    }

    fn has(self, other: Sources) -> bool {
        self.0 & other.0 != 0
    }
}

/// What a step may raise capabilities and records from.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Allowed<'tcx> {
    pub(crate) capabilities: Sources,
    pub(crate) records: Sources,
    pub(crate) fresh: Option<(Place<'tcx>, CapabilityKind)>,
}

impl<'tcx> Allowed<'tcx> {
    pub(crate) const fn new(capabilities: Sources, records: Sources) -> Self {
        Self {
            capabilities,
            records,
            fresh: None,
        }
    }

    pub(crate) const NOTHING: Allowed<'tcx> = Allowed::new(Sources::NONE, Sources::NONE);

    /// The removal of an edge: a loan's end gives back what is recorded, an
    /// unpacking's removal packs its parts into the base.
    pub(crate) const fn removal() -> Self {
        Allowed::new(
            Sources::OWN_REC
                .or(Sources::ANC_REC)
                .or(Sources::DESC_CAP)
                .or(Sources::DESC_REC),
            Sources::NONE,
        )
    }

    /// The post-condition `post` of a statement: a write or an allocation
    /// creates a fresh capability at its place; the others only lower.
    pub(crate) fn post_condition(post: Option<PlaceCondition<'tcx>>) -> Self {
        let fresh = match post {
            Some(PlaceCondition::Capability(place, capability)) => Some((place, capability)),
            Some(PlaceCondition::AllocateOrDeallocate(local)) => {
                Some((local.into(), CapabilityKind::Write))
            }
            _ => None,
        };
        Allowed {
            capabilities: Sources::NONE,
            records: Sources::NONE,
            fresh,
        }
    }
}

/// What applying `action` may raise from, following the action model: an
/// unpacking passes on a share of the base, a pack the meet of the parts; a
/// loan, a freeze or a lend records what the place held; the end of a loan
/// or a freeze gives back what is recorded; the other actions only lower.
pub(crate) fn allowed_for_action<'tcx>(action: &PcgAction<'tcx>) -> Allowed<'tcx> {
    use Sources as S;
    match action {
        PcgAction::Borrow(action) => match &action.kind {
            BorrowPcgActionKind::Weaken(_)
            | BorrowPcgActionKind::WeakenSuspended { .. }
            | BorrowPcgActionKind::ActivateTwoPhaseBorrow { .. }
            | BorrowPcgActionKind::LabelLifetimeProjection(_) => Allowed::NOTHING,
            // A freeze of an unpacked place packs what its parts hold; the
            // `freeze` rule rejects that composite, and conservation only
            // asks for a source.
            BorrowPcgActionKind::Freeze { .. } => Allowed::new(
                S::OWN_CAP.or(S::DESC_CAP),
                S::OWN_CAP.or(S::DESC_CAP).or(S::DESC_REC),
            ),
            BorrowPcgActionKind::Unfreeze { .. } | BorrowPcgActionKind::Refreeze { .. } => {
                Allowed::new(S::OWN_REC.or(S::ANC_REC), S::ANC_REC)
            }
            BorrowPcgActionKind::AddEdge { .. } => {
                Allowed::new(S::OWN_CAP.or(S::ANC_CAP), S::OWN_CAP)
            }
            BorrowPcgActionKind::Lend { .. } => {
                Allowed::new(S::NONE, S::OWN_CAP.or(S::OWN_REC).or(S::ANC_CAP))
            }
            BorrowPcgActionKind::RemoveEdge(_) => Allowed::removal(),
            // A label gives back what the labelled value's loans recorded;
            // the `label` rule rejects that composite.
            BorrowPcgActionKind::LabelPlace(_) => {
                Allowed::new(S::OWN_REC.or(S::ANC_REC).or(S::DESC_CAP), S::NONE)
            }
            BorrowPcgActionKind::UnpackSuspended { .. } => Allowed::new(S::NONE, S::ANC_REC),
            BorrowPcgActionKind::PackSuspended { .. } => Allowed::new(S::NONE, S::DESC_REC),
        },
        PcgAction::Owned(action) => match action.kind {
            RepackOp::Expand(_) | RepackOp::DerefShallowInit(..) => {
                Allowed::new(S::OWN_CAP.or(S::ANC_CAP), S::NONE)
            }
            RepackOp::Collapse(_) => Allowed::new(S::DESC_CAP, S::NONE),
            RepackOp::StorageDead(_) => Allowed::NOTHING,
        },
    }
}

/// The rises among `changes` from `before` to `after` that `allowed` gives no
/// source for.
pub(crate) fn check<'a, 'tcx: 'a>(
    before: &PlaceCapabilities<'tcx>,
    after: &PlaceCapabilities<'tcx>,
    changes: &[Change<'tcx>],
    allowed: Allowed<'tcx>,
    ctxt: CompilerCtxt<'a, 'tcx>,
) -> Vec<Violation> {
    let mut violations = vec![];
    for &Change {
        place, old, new, ..
    } in changes
    {
        let Some(new) = new else {
            continue;
        };
        if place.contains_unsafe_deref(ctxt) || !rises(old, new) {
            continue;
        }
        if allowed
            .fresh
            .is_some_and(|(fresh, capability)| fresh == place && new <= capability)
        {
            continue;
        }
        match source(before, place, new, allowed.capabilities, ctxt) {
            None => violations.push(Violation::new(
                "conservation",
                format!(
                    "{} rises from {} to {} with no source",
                    place.display_string(ctxt),
                    show(old),
                    show(Some(new))
                ),
            )),
            Some(Sources::OWN_REC | Sources::ANC_REC) if !new.is_read() => {
                if let Some((holder, record)) = after.iter_suspended().find(|(holder, record)| {
                    holder.is_prefix_of(place) && holder.share_at(*record, place, ctxt).is_some()
                }) {
                    violations.push(Violation::new(
                        "conservation",
                        format!(
                            "{} gets {} back while {} still records {}",
                            place.display_string(ctxt),
                            show(Some(new)),
                            holder.display_string(ctxt),
                            show(Some(record))
                        ),
                    ));
                }
            }
            Some(_) => {}
        }
    }
    for &Change {
        place,
        old_record: old,
        new_record: new,
        ..
    } in changes
    {
        let Some(new) = new else {
            continue;
        };
        if place.contains_unsafe_deref(ctxt) || !rises(old, new) {
            continue;
        }
        if source(before, place, new, allowed.records, ctxt).is_none() {
            violations.push(Violation::new(
                "conservation",
                format!(
                    "the record of {} rises from {} to {} with no source",
                    place.display_string(ctxt),
                    show(old),
                    show(Some(new))
                ),
            ));
        }
    }
    violations
}

/// The first of `sources` in `before` that `new` at `place` is at most.
fn source<'a, 'tcx: 'a>(
    before: &PlaceCapabilities<'tcx>,
    place: Place<'tcx>,
    new: CapabilityKind,
    sources: Sources,
    ctxt: CompilerCtxt<'a, 'tcx>,
) -> Option<Sources> {
    let readable = || {
        !before
            .iter_suspended()
            .any(|(q, _)| place.is_strict_prefix_of(q) && before.get(q, ctxt).is_none())
            && !before
                .iter()
                .any(|(q, c)| place.is_strict_prefix_of(q) && c == CapabilityKind::Write)
    };
    let covers = |capability: Option<CapabilityKind>| {
        capability.is_some_and(|c| {
            new <= c
                || new == CapabilityKind::Read
                    && c == CapabilityKind::ShallowExclusive
                    && readable()
        })
    };
    let from_ancestor = |entries: Vec<(Place<'tcx>, CapabilityKind)>| {
        entries.into_iter().any(|(ancestor, capability)| {
            ancestor.is_strict_prefix_of(place)
                && covers(ancestor.share_at(capability, place, ctxt))
        })
    };
    let below = |entries: Vec<(Place<'tcx>, CapabilityKind)>| {
        entries
            .into_iter()
            .filter(|(part, _)| place.is_prefix_of(*part))
            .collect::<Vec<_>>()
    };
    if sources.has(Sources::OWN_CAP) && covers(before.get(place, ctxt)) {
        return Some(Sources::OWN_CAP);
    }
    if sources.has(Sources::OWN_REC) && covers(before.suspended(place)) {
        return Some(Sources::OWN_REC);
    }
    if sources.has(Sources::ANC_CAP) && from_ancestor(before.iter().collect()) {
        return Some(Sources::ANC_CAP);
    }
    if sources.has(Sources::ANC_REC) && from_ancestor(before.iter_suspended().collect()) {
        return Some(Sources::ANC_REC);
    }
    if sources.has(Sources::DESC_CAP) {
        let lent_part = before.iter_suspended().any(|(part, _)| {
            place.is_strict_prefix_of(part)
                && place.in_storage(part, ctxt)
                && before.get(part, ctxt).is_none()
        });
        if !lent_part && covers(packed(place, &below(before.iter().collect()), ctxt).0) {
            return Some(Sources::DESC_CAP);
        }
    }
    if sources.has(Sources::DESC_REC)
        && covers(packed(place, &outermost(&below(covered(before)), ctxt), ctxt).0)
    {
        return Some(Sources::DESC_REC);
    }
    None
}

/// What each place records or, recording nothing, holds: what it gets back
/// once its loans and freezes end.
fn covered<'tcx>(capabilities: &PlaceCapabilities<'tcx>) -> Vec<(Place<'tcx>, CapabilityKind)> {
    capabilities
        .iter()
        .filter(|(p, _)| capabilities.suspended(*p).is_none())
        .chain(capabilities.iter_suspended())
        .collect()
}

/// The entries not stored in another entry: a read copy counts through the
/// frozen place it is a copy of.
fn outermost<'a, 'tcx: 'a>(
    entries: &[(Place<'tcx>, CapabilityKind)],
    ctxt: CompilerCtxt<'a, 'tcx>,
) -> Vec<(Place<'tcx>, CapabilityKind)> {
    entries
        .iter()
        .copied()
        .filter(|(p, _)| {
            !entries
                .iter()
                .any(|(q, _)| q.is_strict_prefix_of(*p) && q.in_storage(*p, ctxt))
        })
        .collect()
}
