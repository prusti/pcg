//! The per-action checks: what each action may change and how, compared on
//! snapshots of the state before and after it.
//!
//! Every action is single-purpose (the README's principle 5): it changes the
//! capabilities and records of the places it names and of their parts only
//! (the end of a loan and a label also those of the record holders above
//! them, which get back what they recorded), lists every capability change it
//! makes, and makes exactly the change its kind defines:
//! - Freeze: E to R on a place that holds E itself, recording the E;
//! - Weaken: to `to` on a place that records nothing (applying it asserts
//!   that the place holds `from` and that `to` is lower);
//! - an owned expansion gives each part the share of what the base holds; a
//!   collapse gives the base the meet of what all its parts hold, and nothing
//!   if a part holds nothing;
//! - a borrow's edge takes from the lender exactly what the borrow kind takes:
//!   all of it for a mutable borrow that is not two-phase, nothing for a
//!   shared or two-phase borrow, whose place is frozen;
//! - a dereference gives the referent at most the reference's share;
//! - a label changes no capability;
//! - the preconditions of `Unfreeze`, `Lend`, `UnpackSuspended` and
//!   `PackSuspended`.
//!
//! An action applied while another is being applied (the unpacking of a
//! record when a loan ends) is checked on its own, and its changes are not
//! counted against the action it is part of.
//!
//! Places behind a raw pointer dereference are exempt: their capabilities do
//! not come from the pointer (principle 7).

use std::borrow::Cow;

use itertools::Itertools;

use super::{conservation, fail, ledger, show, show_state};
use crate::{
    action::{BorrowPcgAction, PcgAction},
    borrow_pcg::{
        action::BorrowPcgActionKind, borrow_pcg_edge::LocalNode, edge::kind::BorrowPcgEdgeKind,
        edge_data::EdgeData, graph::BorrowsGraph, validity_conditions::ValidityConditions,
    },
    owned_pcg::RepackOp,
    pcg::{
        CapabilityKind,
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesReader},
    },
    rustc_interface::middle::mir,
    utils::{
        CompilerCtxt, PcgSettings, Place, PlaceLike,
        data_structures::{HashMap as DataHashMap, HashSet},
        display::DisplayWithCompilerCtxt,
    },
};

/// The part of a PCG state that actions change: capabilities, records and
/// the edges of the borrow graph. A snapshot taken before an action owns a
/// copy; the state after it is read in place.
#[derive(Clone)]
pub(crate) struct Snapshot<'s, 'tcx> {
    pub(crate) capabilities: Cow<'s, PlaceCapabilities<'tcx>>,
    pub(crate) edges: Edges<'s, 'tcx>,
}

/// The edges of a [`Snapshot`], with their conditions: a copy (cloned
/// without hashing the edges again), or the graph itself.
#[derive(Clone)]
pub(crate) enum Edges<'s, 'tcx> {
    Copy(DataHashMap<BorrowPcgEdgeKind<'tcx>, ValidityConditions>),
    Graph(&'s BorrowsGraph<'tcx>),
}

impl<'tcx> Edges<'_, 'tcx> {
    fn map(&self) -> &DataHashMap<BorrowPcgEdgeKind<'tcx>, ValidityConditions> {
        match self {
            Edges::Copy(edges) => edges,
            Edges::Graph(graph) => &graph.edges,
        }
    }

    fn contains(&self, edge: &BorrowPcgEdgeKind<'tcx>) -> bool {
        self.map().contains_key(edge)
    }

    fn iter(&self) -> impl Iterator<Item = &BorrowPcgEdgeKind<'tcx>> + '_ {
        self.map().keys()
    }

    /// The edges of `self` that `other` lacks.
    fn difference<'e>(
        &'e self,
        other: &'e Edges<'_, 'tcx>,
    ) -> impl Iterator<Item = &'e BorrowPcgEdgeKind<'tcx>> + 'e {
        self.iter().filter(move |edge| !other.contains(edge))
    }
}

impl<'tcx> Snapshot<'tcx, 'tcx> {
    /// A copy of the state `capabilities` and `graph`.
    pub(crate) fn copy(capabilities: &PlaceCapabilities<'tcx>, graph: &BorrowsGraph<'tcx>) -> Self {
        Self {
            capabilities: Cow::Owned(capabilities.clone()),
            edges: Edges::Copy(graph.edges.clone()),
        }
    }

    /// Sets what `from` and `to` differ in to its value in `to`: the effect of
    /// an action applied while this snapshot's action is being applied.
    fn apply_difference(&mut self, from: &Snapshot<'_, 'tcx>, to: &Snapshot<'_, 'tcx>) {
        let capabilities = self.capabilities.to_mut();
        for change in changes(&from.capabilities, &to.capabilities) {
            match change.new {
                Some(new) => capabilities.map.insert(change.place, new),
                None => capabilities.map.remove(&change.place),
            };
            match change.new_record {
                Some(new) => capabilities.suspended.insert(change.place, new),
                None => capabilities.suspended.remove(&change.place),
            };
        }
        let Edges::Copy(edges) = &mut self.edges else {
            unreachable!("a copied snapshot copies its edges")
        };
        for edge in from.edges.difference(&to.edges) {
            edges.remove(edge);
        }
        for (edge, conditions) in to.edges.map() {
            if !from.edges.contains(edge) {
                edges.insert(edge.clone(), conditions.clone());
            }
        }
    }
}

/// A place whose capability or record differs between two states.
#[derive(Clone, Copy)]
pub(crate) struct Change<'tcx> {
    pub(crate) place: Place<'tcx>,
    pub(crate) old: Option<CapabilityKind>,
    pub(crate) new: Option<CapabilityKind>,
    pub(crate) old_record: Option<CapabilityKind>,
    pub(crate) new_record: Option<CapabilityKind>,
}

/// The places whose capability or record differs between `before` and
/// `after`, found in one pass over each.
pub(crate) fn changes<'tcx>(
    before: &PlaceCapabilities<'tcx>,
    after: &PlaceCapabilities<'tcx>,
) -> Vec<Change<'tcx>> {
    let mut changed = HashSet::default();
    for (a, b) in [(&before.map, &after.map), (&after.map, &before.map)]
        .into_iter()
        .chain([
            (&before.suspended, &after.suspended),
            (&after.suspended, &before.suspended),
        ])
    {
        for (place, capability) in a {
            if b.get(place) != Some(capability) {
                changed.insert(*place);
            }
        }
    }
    changed
        .into_iter()
        .map(|place| Change {
            place,
            old: before.map.get(&place).copied(),
            new: after.map.get(&place).copied(),
            old_record: before.suspended.get(&place).copied(),
            new_record: after.suspended.get(&place).copied(),
        })
        .collect()
}

impl<'s, 'tcx> Snapshot<'s, 'tcx> {
    /// The state `capabilities` and `graph`, read in place.
    pub(crate) fn of(
        capabilities: &'s PlaceCapabilities<'tcx>,
        graph: &'s BorrowsGraph<'tcx>,
    ) -> Self {
        Self {
            capabilities: Cow::Borrowed(capabilities),
            edges: Edges::Graph(graph),
        }
    }
}

/// The actions being applied, innermost last: the state before each, as it
/// was and, once an action was applied within it, with that action's effect.
#[derive(Default)]
pub(crate) struct OpenActions<'tcx> {
    open: Vec<(Snapshot<'tcx, 'tcx>, Option<Snapshot<'tcx, 'tcx>>)>,
}

impl<'tcx> OpenActions<'tcx> {
    /// Starts checking an action applied to the state `capabilities` and
    /// `graph`, if `settings` enable the checks. Returns the depth to pass to
    /// [`Self::end`].
    pub(crate) fn begin(
        &mut self,
        capabilities: &PlaceCapabilities<'tcx>,
        graph: &BorrowsGraph<'tcx>,
        settings: &PcgSettings,
    ) -> Option<usize> {
        if !super::enabled(settings) {
            return None;
        }
        self.open.push((Snapshot::copy(capabilities, graph), None));
        Some(self.open.len() - 1)
    }

    /// Checks `action`, begun at `depth`, which has left the state
    /// `capabilities` and `graph`.
    pub(crate) fn end<'a>(
        &mut self,
        depth: Option<usize>,
        action: &PcgAction<'tcx>,
        capabilities: &PlaceCapabilities<'tcx>,
        graph: &BorrowsGraph<'tcx>,
        location: mir::Location,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) where
        'tcx: 'a,
    {
        let Some(depth) = depth else {
            return;
        };
        self.open.truncate(depth + 1);
        let Some((original, own)) = self.open.pop() else {
            return;
        };
        let after = Snapshot::of(capabilities, graph);
        let holders = comeback_holders(&original, action, &named(action, ctxt));
        check_action(
            own.as_ref().unwrap_or(&original),
            &after,
            action,
            &holders,
            location,
            ctxt,
        );
        if let Some((parent, parent_own)) = self.open.last_mut() {
            parent_own
                .get_or_insert_with(|| parent.clone())
                .apply_difference(&original, &after);
        }
    }
}

/// A violation of a rule named `check`.
pub(crate) struct Violation {
    pub(crate) check: &'static str,
    pub(crate) message: String,
}

impl Violation {
    pub(crate) fn new(check: &'static str, message: String) -> Self {
        Self { check, message }
    }
}

/// Checks that `action` turned `before` into `after` as its kind defines;
/// `holders` are its [`comeback_holders`].
pub(crate) fn check_action<'a, 'tcx: 'a>(
    before: &Snapshot<'_, 'tcx>,
    after: &Snapshot<'_, 'tcx>,
    action: &PcgAction<'tcx>,
    holders: &[Place<'tcx>],
    location: mir::Location,
    ctxt: CompilerCtxt<'a, 'tcx>,
) {
    let changes = changes(&before.capabilities, &after.capabilities)
        .into_iter()
        .filter(|change| !change.place.contains_unsafe_deref(ctxt))
        .collect::<Vec<_>>();
    let mut violations = frame(before, after, action, &changes, holders, ctxt);
    violations.extend(kind_rules(before, after, action, &changes, holders, ctxt));
    violations.extend(conservation::check(
        &before.capabilities,
        &after.capabilities,
        &changes,
        conservation::allowed_for_action(action),
        ctxt,
    ));
    violations.extend(ledger::observe(
        &before.capabilities,
        &after.capabilities,
        action,
        ctxt,
    ));
    if violations.is_empty() {
        return;
    }
    let names = named(action, ctxt);
    let related = |p: Place<'tcx>| names.iter().any(|n| n.place.local == p.local);
    for violation in violations {
        fail(
            ctxt,
            violation.check,
            &format!(
                "{location:?}: {}: {}\n  before: {}\n  after:  {}",
                action.debug_line(ctxt),
                violation.message,
                show_state(&before.capabilities, related, ctxt),
                show_state(&after.capabilities, related, ctxt)
            ),
        );
    }
}

/// A place an action names, whose capability and record it may change; with
/// `parts`, also those of the places in its value.
struct Named<'tcx> {
    place: Place<'tcx>,
    parts: bool,
}

/// The current places that `edge` blocks and is blocked by.
fn edge_places<'a, 'tcx: 'a>(
    edge: &BorrowPcgEdgeKind<'tcx>,
    ctxt: CompilerCtxt<'a, 'tcx>,
) -> (Vec<Place<'tcx>>, Vec<Place<'tcx>>) {
    (
        edge.blocked_nodes(ctxt)
            .filter_map(|node| node.as_current_place())
            .collect(),
        edge.blocked_by_nodes(ctxt)
            .filter_map(LocalNode::as_current_place)
            .collect(),
    )
}

/// The places `action` names.
fn named<'a, 'tcx: 'a>(action: &PcgAction<'tcx>, ctxt: CompilerCtxt<'a, 'tcx>) -> Vec<Named<'tcx>> {
    let with_parts = |place| Named { place, parts: true };
    let only = |place| Named {
        place,
        parts: false,
    };
    match action {
        PcgAction::Borrow(action) => match &action.kind {
            BorrowPcgActionKind::LabelLifetimeProjection(_) => vec![],
            BorrowPcgActionKind::Weaken(weaken) => vec![only(weaken.place)],
            BorrowPcgActionKind::WeakenSuspended { place, .. }
            | BorrowPcgActionKind::Freeze { place } => vec![only(*place)],
            BorrowPcgActionKind::Unfreeze { place }
            | BorrowPcgActionKind::Refreeze { place, .. }
            | BorrowPcgActionKind::UnpackSuspended { place, .. }
            | BorrowPcgActionKind::PackSuspended { place } => vec![with_parts(*place)],
            BorrowPcgActionKind::ActivateTwoPhaseBorrow { borrow } => borrow
                .blocked_place
                .as_current_place()
                .into_iter()
                .map(only)
                .collect(),
            BorrowPcgActionKind::LabelPlace(label) => vec![with_parts(label.place)],
            BorrowPcgActionKind::RemoveEdge(edge) | BorrowPcgActionKind::AddEdge { edge } => {
                let (blocked, blocked_by) = edge_places(edge.kind(), ctxt);
                blocked
                    .into_iter()
                    .chain(blocked_by)
                    .map(with_parts)
                    .collect()
            }
            BorrowPcgActionKind::Lend { place, edge } => {
                let (blocked, blocked_by) = edge_places(edge.kind(), ctxt);
                std::iter::once(*place)
                    .chain(blocked)
                    .chain(blocked_by)
                    .map(with_parts)
                    .collect()
            }
        },
        PcgAction::Owned(action) => match action.kind {
            RepackOp::Expand(expand) => vec![with_parts(expand.from())],
            RepackOp::Collapse(collapse) => vec![with_parts(collapse.to())],
            RepackOp::DerefShallowInit(from, _) => vec![with_parts(from)],
            RepackOp::StorageDead(local) => vec![with_parts(local.into())],
        },
    }
}

/// The places that record what a loan or freeze took and get it back when
/// `action` ends the loan (a `RemoveEdge`) or labels the lent value (a
/// `LabelPlace`): the record holders in `before` at or above the places the
/// action names. A record is kept where the capability was lent, which can be
/// a place the loan's edge only blocks a part of (a `Lend` at a join).
fn comeback_holders<'tcx>(
    before: &Snapshot<'_, 'tcx>,
    action: &PcgAction<'tcx>,
    names: &[Named<'tcx>],
) -> Vec<Place<'tcx>> {
    if !matches!(
        action,
        PcgAction::Borrow(BorrowPcgAction {
            kind: BorrowPcgActionKind::RemoveEdge(_) | BorrowPcgActionKind::LabelPlace(_),
            ..
        })
    ) {
        return vec![];
    }
    before
        .capabilities
        .suspended
        .keys()
        .copied()
        .filter(|holder| names.iter().any(|n| holder.is_prefix_of(n.place)))
        .collect()
}

/// The frame condition: `action` changes only the capabilities and records
/// of the places it names, and lists each capability it changes with the
/// capability the place has after it. The borrow graph gains exactly the
/// edge an `AddEdge` or `Lend` adds and loses exactly the edge a
/// `RemoveEdge` removes; only labels change it otherwise.
fn frame<'a, 'tcx: 'a>(
    before: &Snapshot<'_, 'tcx>,
    after: &Snapshot<'_, 'tcx>,
    action: &PcgAction<'tcx>,
    changes: &[Change<'tcx>],
    holders: &[Place<'tcx>],
    ctxt: CompilerCtxt<'a, 'tcx>,
) -> Vec<Violation> {
    let mut violations = vec![];
    let names = named(action, ctxt);
    let in_frame = |p: Place<'tcx>| {
        names
            .iter()
            .any(|n| n.place == p || (n.parts && n.place.is_prefix_of(p)))
            || holders.iter().any(|h| h.is_prefix_of(p))
    };
    let listed = super::listed_changes(action);
    for &Change {
        place,
        old,
        new,
        old_record,
        new_record,
    } in changes
    {
        if !in_frame(place) {
            violations.push(Violation::new(
                "frame",
                format!(
                    "changes {}, which it does not name, from {}/record {} to {}/record {}",
                    place.display_string(ctxt),
                    show(old),
                    show(old_record),
                    show(new),
                    show(new_record)
                ),
            ));
        }
        if old != new && !listed.iter().any(|(p, c)| p == place && c == new) {
            violations.push(Violation::new(
                "frame",
                format!(
                    "changes {} from {} to {} without listing it",
                    place.display_string(ctxt),
                    show(old),
                    show(new)
                ),
            ));
        }
    }
    for (place, capability) in listed.iter() {
        if after.capabilities.get(place, ctxt) != capability {
            violations.push(Violation::new(
                "frame",
                format!(
                    "lists {}: {}, but it has {}",
                    place.display_string(ctxt),
                    show(capability),
                    show(after.capabilities.get(place, ctxt))
                ),
            ));
        }
    }
    let added = after.edges.difference(&before.edges).collect::<Vec<_>>();
    let removed = before.edges.difference(&after.edges).collect::<Vec<_>>();
    let show_edges = |edges: &[&BorrowPcgEdgeKind<'tcx>]| {
        edges.iter().map(|e| e.display_string(ctxt)).join(", ")
    };
    let (may_add, may_remove, relabels): (Option<&BorrowPcgEdgeKind<'tcx>>, Option<_>, bool) =
        match action {
            PcgAction::Borrow(action) => match &action.kind {
                BorrowPcgActionKind::AddEdge { edge } | BorrowPcgActionKind::Lend { edge, .. } => {
                    (Some(edge.kind()), None, false)
                }
                BorrowPcgActionKind::RemoveEdge(edge) => (None, Some(edge.kind()), false),
                BorrowPcgActionKind::LabelPlace(_)
                | BorrowPcgActionKind::LabelLifetimeProjection(_) => (None, None, true),
                _ => (None, None, false),
            },
            PcgAction::Owned(_) => (None, None, false),
        };
    if !relabels {
        let unexpected_added = added
            .iter()
            .copied()
            .filter(|e| Some(*e) != may_add)
            .collect::<Vec<_>>();
        let unexpected_removed = removed
            .iter()
            .copied()
            .filter(|e| Some(*e) != may_remove)
            .collect::<Vec<_>>();
        if !unexpected_added.is_empty() || !unexpected_removed.is_empty() {
            violations.push(Violation::new(
                "frame",
                format!(
                    "changes the borrow graph beyond its edge: adds [{}], removes [{}]",
                    show_edges(&unexpected_added),
                    show_edges(&unexpected_removed)
                ),
            ));
        }
        if let Some(edge) = may_remove
            && !before.edges.contains(edge)
        {
            violations.push(Violation::new(
                "frame",
                "removes an edge that is not in the graph".to_owned(),
            ));
        }
    }
    violations
}

/// The capabilities and records of `snapshot` as a lookup.
struct State<'s, 'tcx> {
    capabilities: &'s PlaceCapabilities<'tcx>,
}

impl<'tcx> State<'_, 'tcx> {
    fn get(&self, place: Place<'tcx>) -> Option<CapabilityKind> {
        self.capabilities.map.get(&place).copied()
    }

    fn record(&self, place: Place<'tcx>) -> Option<CapabilityKind> {
        self.capabilities.suspended.get(&place).copied()
    }

    /// The strict postfixes of `place` that hold a capability.
    fn holding_parts(&self, place: Place<'tcx>) -> Vec<(Place<'tcx>, CapabilityKind)> {
        self.capabilities
            .iter()
            .filter(|(p, _)| place.is_strict_prefix_of(*p))
            .collect()
    }
}

/// The rules of each action kind.
fn kind_rules<'a, 'tcx: 'a>(
    before: &Snapshot<'_, 'tcx>,
    after: &Snapshot<'_, 'tcx>,
    action: &PcgAction<'tcx>,
    changes: &[Change<'tcx>],
    holders: &[Place<'tcx>],
    ctxt: CompilerCtxt<'a, 'tcx>,
) -> Vec<Violation> {
    let changed = |keep: &dyn Fn(&Change<'tcx>) -> bool| {
        changes
            .iter()
            .filter(|change| keep(change))
            .map(|change| change.place)
            .collect::<Vec<_>>()
    };
    let b = State {
        capabilities: &before.capabilities,
    };
    let a = State {
        capabilities: &after.capabilities,
    };
    let mut violations = vec![];
    let mut require = |check: &'static str, holds: bool, message: &dyn Fn() -> String| {
        if !holds {
            violations.push(Violation::new(check, message()));
        }
    };
    let d = |p: Place<'tcx>| p.display_string(ctxt);
    match action {
        PcgAction::Borrow(action) => match &action.kind {
            BorrowPcgActionKind::Weaken(weaken) => {
                let place = weaken.place;
                require("weaken", a.get(place) == Some(weaken.to), &|| {
                    format!("{} has {} afterwards", d(place), show(a.get(place)))
                });
                require(
                    "weaken",
                    b.record(place).is_none() && a.record(place).is_none(),
                    &|| {
                        format!(
                            "{} records {} (afterwards {}): a lent or frozen place is not weakened",
                            d(place),
                            show(b.record(place)),
                            show(a.record(place))
                        )
                    },
                );
            }
            BorrowPcgActionKind::Freeze { place } => {
                let place = *place;
                require(
                    "freeze",
                    b.get(place) == Some(CapabilityKind::Exclusive),
                    &|| {
                        format!(
                            "{} holds {} (parts: {}), not E",
                            d(place),
                            show(b.get(place)),
                            b.holding_parts(place)
                                .iter()
                                .map(|(p, c)| format!("{}: {}", d(*p), show(Some(*c))))
                                .join(", ")
                        )
                    },
                );
                require(
                    "freeze",
                    a.get(place) == Some(CapabilityKind::Read)
                        && a.record(place) == Some(CapabilityKind::Exclusive),
                    &|| {
                        format!(
                            "{} has {}/record {} afterwards, not R/record E",
                            d(place),
                            show(a.get(place)),
                            show(a.record(place))
                        )
                    },
                );
                let others = changed(&|change| change.place != place);
                require("freeze", others.is_empty(), &|| {
                    format!("also changes {}", others.iter().map(|p| d(*p)).join(", "))
                });
            }
            BorrowPcgActionKind::Unfreeze { place } => {
                let place = *place;
                require(
                    "unfreeze",
                    b.get(place) == Some(CapabilityKind::Read) && b.record(place).is_some(),
                    &|| {
                        format!(
                            "{} holds {}/record {}, not R with a record",
                            d(place),
                            show(b.get(place)),
                            show(b.record(place))
                        )
                    },
                );
                let loans = if place.contains_unsafe_deref(ctxt) {
                    vec![]
                } else {
                    loans_overlapping(after, place, ctxt)
                };
                require("unfreeze", loans.is_empty(), &|| {
                    format!("{} is still borrowed by {}", d(place), loans.join(", "))
                });
            }
            BorrowPcgActionKind::Refreeze { place, to } => {
                let place = *place;
                require(
                    "refreeze",
                    b.get(place) == Some(CapabilityKind::Read) && b.record(place).is_some(),
                    &|| {
                        format!(
                            "{} holds {}/record {}, not R with a record",
                            d(place),
                            show(b.get(place)),
                            show(b.record(place))
                        )
                    },
                );
                for &t in to {
                    require(
                        "refreeze",
                        place.is_strict_prefix_of(t)
                            && a.get(t) == Some(CapabilityKind::Read)
                            && a.record(t).is_some(),
                        &|| {
                            format!(
                                "{} is not a frozen part of {} afterwards ({}/record {})",
                                d(t),
                                d(place),
                                show(a.get(t)),
                                show(a.record(t))
                            )
                        },
                    );
                }
            }
            BorrowPcgActionKind::ActivateTwoPhaseBorrow { borrow } => {
                if let Some(place) = borrow.blocked_place.as_current_place() {
                    require(
                        "activate",
                        a.get(place).is_none() && a.record(place) == b.record(place),
                        &|| {
                            format!(
                                "{} has {}/record {} afterwards, not none/record {}",
                                d(place),
                                show(a.get(place)),
                                show(a.record(place)),
                                show(b.record(place))
                            )
                        },
                    );
                }
            }
            BorrowPcgActionKind::AddEdge { edge } => {
                add_edge_rules(&b, &a, edge.kind(), &mut require, ctxt);
            }
            BorrowPcgActionKind::RemoveEdge(edge) => {
                let (blocked, _) = edge_places(edge.kind(), ctxt);
                let risen = changed(&|change| {
                    change.new.is_some_and(|new| super::rises(change.old, new))
                        && !blocked
                            .iter()
                            .chain(holders)
                            .any(|q| q.is_prefix_of(change.place))
                });
                require("remove-edge", risen.is_empty(), &|| {
                    format!(
                        "gives capabilities to {}, which the edge does not block",
                        risen.iter().map(|p| d(*p)).join(", ")
                    )
                });
            }
            BorrowPcgActionKind::Lend { place, .. } => {
                let place = *place;
                require(
                    "lend",
                    b.get(place).is_some() || b.record(place).is_some(),
                    &|| format!("{} holds and records nothing", d(place)),
                );
                require(
                    "lend",
                    a.get(place).is_none() && a.record(place).is_some(),
                    &|| {
                        format!(
                            "{} has {}/record {} afterwards, not none with a record",
                            d(place),
                            show(a.get(place)),
                            show(a.record(place))
                        )
                    },
                );
            }
            BorrowPcgActionKind::LabelPlace(_)
            | BorrowPcgActionKind::LabelLifetimeProjection(_) => {
                let changed = changed(&|change| change.old != change.new);
                require("label", changed.is_empty(), &|| {
                    format!(
                        "changes the capabilities of {}",
                        changed
                            .iter()
                            .map(|p| format!(
                                "{} ({} to {})",
                                d(*p),
                                show(b.get(*p)),
                                show(a.get(*p))
                            ))
                            .join(", ")
                    )
                });
            }
            BorrowPcgActionKind::WeakenSuspended { .. } => {}
            BorrowPcgActionKind::UnpackSuspended { place, parts } => {
                let place = *place;
                require("unpack-suspended", b.record(place).is_some(), &|| {
                    format!("{} records nothing", d(place))
                });
                if let Some(&first) = parts.first()
                    && let Ok(expansion) = place.expand_one_level(first, ctxt)
                {
                    let expected = expansion.expansion().into_iter().collect::<HashSet<_>>();
                    let given = parts.iter().copied().collect::<HashSet<_>>();
                    require("unpack-suspended", expected == given, &|| {
                        format!(
                            "unpacks to [{}], not all of [{}]",
                            parts.iter().map(|p| d(*p)).join(", "),
                            expected.iter().map(|p| d(*p)).join(", ")
                        )
                    });
                }
                let changed = changed_capabilities(changes, ctxt);
                require("unpack-suspended", changed.is_empty(), &|| {
                    format!("changes the capabilities of {}", changed.join(", "))
                });
            }
            BorrowPcgActionKind::PackSuspended { place } => {
                let place = *place;
                let above_read = b
                    .capabilities
                    .iter_suspended()
                    .filter(|&(p, _)| place.is_strict_prefix_of(p))
                    .filter_map(|(p, _)| Some((p, b.get(p).filter(|c| !c.is_read())?)))
                    .collect::<Vec<_>>();
                require("pack-suspended", above_read.is_empty(), &|| {
                    format!(
                        "packs the records of parts holding more than R: {}",
                        above_read
                            .iter()
                            .map(|(p, c)| format!("{}: {}", d(*p), show(Some(*c))))
                            .join(", ")
                    )
                });
                let changed = changed_capabilities(changes, ctxt);
                require("pack-suspended", changed.is_empty(), &|| {
                    format!("changes the capabilities of {}", changed.join(", "))
                });
            }
        },
        PcgAction::Owned(owned) => match owned.kind {
            RepackOp::Expand(expand) => {
                let base = expand.from();
                let parts = expand.target_places(ctxt);
                let held = b.get(base);
                require("expand", held.is_some(), &|| {
                    format!("expands {}, which holds nothing", d(base))
                });
                if let Some(held) = held {
                    for &part in &parts {
                        let share = if expand.capability().is_read() {
                            Some(CapabilityKind::Read)
                        } else {
                            base.share_at(held, part, ctxt)
                        };
                        require("expand", a.get(part) == share, &|| {
                            format!(
                                "gives {} {} from {}: {}, not its share {}",
                                d(part),
                                show(a.get(part)),
                                d(base),
                                show(Some(held)),
                                show(share)
                            )
                        });
                    }
                }
            }
            RepackOp::Collapse(collapse) => {
                let base = collapse.to();
                let expansion = base.expansion(collapse.guide(), ctxt);
                if let Ok(parts) = base.expansion_places(&expansion, ctxt) {
                    let held = parts.iter().map(|p| b.get(*p)).collect::<Option<Vec<_>>>();
                    let packed =
                        held.and_then(|held| {
                            held.into_iter()
                                .try_fold(None, |acc: Option<CapabilityKind>, c| match acc {
                                    None => Some(Some(c)),
                                    Some(acc) => acc.minimum(c).map(Some),
                                })
                        });
                    let still_expanded =
                        a.get(base).is_none() && parts.iter().all(|p| a.get(*p) == b.get(*p));
                    if !still_expanded {
                        require(
                            "collapse",
                            matches!(packed, Some(Some(c)) if a.get(base) == Some(c)),
                            &|| {
                                format!(
                                    "gives {} {} from parts [{}]: not their meet (none if a part holds nothing or they are incomparable)",
                                    d(base),
                                    show(a.get(base)),
                                    parts
                                        .iter()
                                        .map(|p| format!("{}: {}", d(*p), show(b.get(*p))))
                                        .join(", ")
                                )
                            },
                        );
                    }
                }
            }
            RepackOp::StorageDead(local) => {
                let left = after
                    .capabilities
                    .map
                    .keys()
                    .chain(after.capabilities.suspended.keys())
                    .filter(|p| p.local == local)
                    .map(|p| d(*p))
                    .collect::<Vec<_>>();
                require("storage-dead", left.is_empty(), &|| {
                    format!("leaves {} holding or recording something", left.join(", "))
                });
            }
            RepackOp::DerefShallowInit(..) => {}
        },
    }
    violations
}

/// The rules of adding `edge`.
fn add_edge_rules<'a, 'tcx: 'a>(
    b: &State<'_, 'tcx>,
    a: &State<'_, 'tcx>,
    edge: &BorrowPcgEdgeKind<'tcx>,
    require: &mut impl FnMut(&'static str, bool, &dyn Fn() -> String),
    ctxt: CompilerCtxt<'a, 'tcx>,
) {
    let d = |p: Place<'tcx>| p.display_string(ctxt);
    match edge {
        BorrowPcgEdgeKind::Borrow(borrow) => {
            let Some(lender) = borrow.blocked_place.as_current_place() else {
                return;
            };
            if lender.contains_unsafe_deref(ctxt) {
                return;
            }
            let takes_all = matches!(
                borrow.kind(),
                mir::BorrowKind::Mut {
                    kind: mir::MutBorrowKind::Default | mir::MutBorrowKind::ClosureCapture
                }
            );
            if takes_all {
                require(
                    "borrow",
                    b.get(lender).is_some()
                        && a.get(lender).is_none()
                        && a.record(lender) == b.get(lender),
                    &|| {
                        format!(
                            "a mutable borrow takes all of {}: it holds {} before and {}/record {} after",
                            d(lender),
                            show(b.get(lender)),
                            show(a.get(lender)),
                            show(a.record(lender))
                        )
                    },
                );
            } else {
                require(
                    "borrow",
                    b.get(lender) == Some(CapabilityKind::Read)
                        && a.get(lender) == b.get(lender)
                        && a.record(lender) == b.record(lender),
                    &|| {
                        format!(
                            "a shared or two-phase borrow takes nothing from {}, which must be frozen: \
                             it holds {}/record {} before and {}/record {} after",
                            d(lender),
                            show(b.get(lender)),
                            show(b.record(lender)),
                            show(a.get(lender)),
                            show(a.record(lender))
                        )
                    },
                );
            }
        }
        BorrowPcgEdgeKind::Deref(deref) => {
            let (Some(reference), Some(referent)) = (
                deref.blocked_place.as_current_place(),
                deref.deref_place.as_current_place(),
            ) else {
                return;
            };
            if referent.contains_unsafe_deref(ctxt) {
                return;
            }
            let held = b.get(reference);
            let share = held.and_then(|held| reference.share_at(held, referent, ctxt));
            require(
                "deref",
                a.get(referent)
                    .is_none_or(|got| share.is_some_and(|share| got <= share)),
                &|| {
                    format!(
                        "gives {} {}, more than the share {} of {}: {}",
                        d(referent),
                        show(a.get(referent)),
                        show(share),
                        d(reference),
                        show(held)
                    )
                },
            );
        }
        BorrowPcgEdgeKind::BorrowPcgExpansion(_) => {
            let (blocked, blocked_by) = edge_places(edge, ctxt);
            for base in blocked {
                let held = b.get(base);
                for &part in &blocked_by {
                    if part.contains_unsafe_deref(ctxt) {
                        continue;
                    }
                    let share = held.and_then(|held| base.share_at(held, part, ctxt));
                    require(
                        "expand",
                        a.get(part)
                            .is_none_or(|got| share.is_some_and(|share| got <= share)),
                        &|| {
                            format!(
                                "gives {} {}, more than the share {} of {}: {}",
                                d(part),
                                show(a.get(part)),
                                show(share),
                                d(base),
                                show(held)
                            )
                        },
                    );
                }
            }
        }
        _ => {}
    }
}

/// The capability changes among `changes`, shown.
fn changed_capabilities<'a, 'tcx: 'a>(
    changes: &[Change<'tcx>],
    ctxt: CompilerCtxt<'a, 'tcx>,
) -> Vec<String> {
    changes
        .iter()
        .filter(|change| change.old != change.new)
        .map(|change| {
            format!(
                "{} ({} to {})",
                change.place.display_string(ctxt),
                show(change.old),
                show(change.new)
            )
        })
        .collect()
}

/// The loans in `snapshot` that block `place`, a place whose value it is in,
/// or a part of its value, where rustc tracks the loan (it is not behind a
/// shared reference or raw pointer), shown.
fn loans_overlapping<'a, 'tcx: 'a>(
    snapshot: &Snapshot<'_, 'tcx>,
    place: Place<'tcx>,
    ctxt: CompilerCtxt<'a, 'tcx>,
) -> Vec<String> {
    snapshot
        .edges
        .iter()
        .filter(|edge| {
            edge.is_loan()
                && edge.blocked_nodes(ctxt).any(|node| {
                    node.as_current_place().is_some_and(|q| {
                        q.in_value(CapabilityKind::Exclusive, place, ctxt)
                            || place.in_value(CapabilityKind::Exclusive, q, ctxt)
                    })
                })
        })
        .map(|edge| edge.display_string(ctxt))
        .collect()
}
