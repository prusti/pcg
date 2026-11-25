//! Tier 2: cross-checks of each PCG state with rustc's dataflow facts at the
//! same program point. The borrow checker is a sound over-approximation of
//! Rust's rules (principle 1), so a capability it rules out is claimed
//! wrongly, and an access it allows that the PCG's capability rules out is a
//! restriction Rust does not have, unless the PCG knows more than borrowck.
//!
//! Over-permission (`over_permission`), at every phase of every location:
//! - `loan`: a capability whose access conflicts with a loan in scope whose
//!   region a local used later still carries (`places_conflict`; E is a
//!   deep write, R a deep read, W and e a shallow write). A loan rustc does
//!   not track (`ignore_borrow`) or that no live local carries is left out;
//! - `uninit`, `uninit-after-drop`: R or E on a place that may be
//!   uninitialised (`MaybeUninitializedPlaces`), or e on one whose own
//!   storage may be;
//! - `storage-dead`: a capability on a local whose storage may be dead
//!   (`MaybeStorageLive`);
//! - `w-live` (over-restriction): W on an initialised place of a local that
//!   is used later (principle 3: a value stays valid until Rust drops it).
//!
//! Over-restriction (`over_restriction`), at block entries and after each
//! statement, the access the PCG's capability rules out though rustc allows
//! it, as rustc would check it at that point:
//! - `under-read`: W or nothing, but rustc allows `&p`;
//! - `under-write`: R, W or nothing, but rustc allows `&mut p`.
//!
//! The over-restriction candidates and the PCG's E and R claims are also
//! the probes of tier 3 ([`Probe`]), which rustc's borrow checker checks for
//! real.

use std::{
    borrow::Cow,
    collections::{BTreeSet, HashSet},
};

use crate::{
    PcgOutput,
    borrow_checker::{InScopeBorrows, RustBorrowCheckerInterface},
    pcg::{CapabilityKind, EvalStmtPhase, Pcg, place_capabilities::PlaceCapabilitiesReader},
    rustc_interface::{
        borrowck::{
            BorrowData, BorrowSet, PlaceConflictBias, PlaceExt, TwoPhaseActivation, places_conflict,
        },
        dataflow::compute_fixpoint,
        index::bit_set::MixedBitSet,
        middle::{
            mir::{self, BorrowKind, Location},
            ty,
        },
        mir_dataflow::{
            impls::{MaybeStorageLive, MaybeUninitializedPlaces, always_storage_live_locals},
            move_paths::{LookupResult, MoveData, MovePathIndex},
        },
    },
    utils::{CompilerCtxt, LocalMutationIsAllowed, Place, display::DisplayWithCompilerCtxt},
};

/// A disagreement of a PCG state with rustc's facts.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Disagreement {
    /// The kind of disagreement (see the module documentation).
    pub class: &'static str,
    /// The place, as the PCG shows it.
    pub place: String,
    /// The program point: a location and phase, or a block entry.
    pub point: String,
    /// The PCG's capability and rustc's fact.
    pub detail: String,
}

/// An access that tier 3 inserts before statement `index` of `block` and
/// borrow checks: `&p` or `&mut p` into a fresh local that is never used.
#[derive(Clone, Debug)]
pub struct Probe {
    /// The block the access is inserted into.
    pub block: usize,
    /// The index of the statement the access is inserted before.
    pub index: usize,
    /// Whether the access is `&mut p` rather than `&p`.
    pub mutable: bool,
    /// The local of `p`.
    pub local: usize,
    /// The projection of `p`, encoded as [`encode_projection`] does.
    pub projection: String,
    /// `under-read` or `under-write` for an over-restriction candidate,
    /// `claim` for an E or R the PCG claims.
    pub class: &'static str,
    /// The place, as the PCG shows it.
    pub place: String,
    /// The PCG state the access checks: a block entry, or the state after
    /// a statement.
    pub point: String,
    /// The capability the PCG gives the place there.
    pub capability: String,
}

/// rustc's per-point facts for the body of `output`.
struct Facts<'mir, 'tcx> {
    body: &'mir mir::Body<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    move_data: MoveData<'tcx>,
    borrow_set: &'mir BorrowSet<'tcx>,
    liveness: UseLiveness,
}

impl<'mir, 'tcx> Facts<'mir, 'tcx> {
    fn new(ctxt: CompilerCtxt<'mir, 'tcx>, bc: &'mir dyn RustBorrowCheckerInterface<'tcx>) -> Self {
        let body = ctxt.body();
        let tcx = ctxt.tcx();
        Self {
            body,
            tcx,
            move_data: MoveData::gather_moves(body, tcx, |_| true),
            borrow_set: bc.borrow_set(),
            liveness: UseLiveness::new(body),
        }
    }

    /// Whether `place` (`deep`: also its parts) may be uninitialised.
    fn maybe_uninit(
        &self,
        uninit: &MixedBitSet<MovePathIndex>,
        place: mir::Place<'tcx>,
        deep: bool,
    ) -> bool {
        let is_uninit = |m: MovePathIndex| uninit.contains(m);
        match self.move_data.rev_lookup.find(place.as_ref()) {
            LookupResult::Exact(m) => {
                any_maybe_uninit(&self.move_data, &is_uninit, m, deep)
                    || self.move_data.move_paths[m]
                        .parents(&self.move_data.move_paths)
                        .any(|(p, _)| is_uninit(p))
            }
            LookupResult::Parent(Some(m)) => {
                is_uninit(m)
                    || self.move_data.move_paths[m]
                        .parents(&self.move_data.move_paths)
                        .any(|(p, _)| is_uninit(p))
            }
            LookupResult::Parent(None) => false,
        }
    }

    /// Whether rustc tracks loans of `borrowed` in its conflict checks. It
    /// ignores loans through a shared reference or a raw pointer
    /// (`ignore_borrow`); its conflict check cannot handle such a loan, which
    /// it keeps only for a reference to a thread-local.
    fn tracks(&self, borrowed: mir::Place<'tcx>) -> bool {
        !borrowed.ignore_borrow(self.tcx, self.body, self.borrow_set.locals_state_at_exit())
            && !borrowed.iter_projections().any(|(base, elem)| {
                matches!(elem, mir::ProjectionElem::Deref)
                    && matches!(
                        base.ty(self.body, self.tcx).ty.kind(),
                        ty::TyKind::RawPtr(..) | ty::TyKind::Ref(_, _, ty::Mutability::Not)
                    )
            })
    }

    /// The loans in `in_scope` that conflict with accessing `place`: a write
    /// (`write`) or a read, deep or (`shallow`) of `place` alone, right
    /// before the statement at `location`, whose activations have not yet
    /// happened. Shared and fake loans and two-phase reservations that are
    /// not active do not conflict with reads.
    fn conflicting_loans(
        &self,
        in_scope: &InScopeBorrows,
        place: mir::Place<'tcx>,
        write: bool,
        shallow: bool,
        location: Location,
    ) -> Vec<&'mir BorrowData<'tcx>> {
        in_scope
            .iter()
            .map(|bi| &self.borrow_set[bi])
            .filter(|b| {
                let bp = b.borrowed_place();
                if bp.local != place.local
                    || !self.tracks(bp)
                    || (shallow && behind_deref_beyond(bp, place))
                    || !places_conflict(self.tcx, self.body, bp, place, PlaceConflictBias::Overlap)
                {
                    return false;
                }
                if write {
                    return true;
                }
                let reserved = match b.activation_location() {
                    TwoPhaseActivation::NotTwoPhase => false,
                    TwoPhaseActivation::ActivatedAt(activation) if activation == location => true,
                    activation => !is_active(self.body, activation, b.reserve_location(), location),
                };
                !(matches!(b.kind(), BorrowKind::Shared | BorrowKind::Fake(_)) || reserved)
            })
            .collect()
    }

    /// The locals used after `location` (`after`) or from it on whose type
    /// carries the region of `borrow`.
    fn carriers(
        &self,
        bc: &dyn RustBorrowCheckerInterface<'tcx>,
        borrow: &BorrowData<'tcx>,
        live: &HashSet<mir::Local>,
    ) -> Vec<mir::Local> {
        self.body
            .local_decls
            .indices()
            .filter(|local| {
                let mut carries = false;
                self.tcx
                    .for_each_free_region(&self.body.local_decls[*local].ty, |r| {
                        if let ty::RegionKind::ReVar(vid) = r.kind()
                            && bc.region_infer_ctxt().eval_outlives(borrow.region(), vid)
                        {
                            carries = true;
                        }
                    });
                carries && live.contains(local)
            })
            .collect()
    }
}

/// rustc's `Shallow(None)` access: it does not reach past a dereference in
/// the borrowed place below the accessed one.
fn behind_deref_beyond<'tcx>(borrowed: mir::Place<'tcx>, access: mir::Place<'tcx>) -> bool {
    borrowed.projection.len() > access.projection.len()
        && borrowed.projection[access.projection.len()..]
            .iter()
            .any(|e| matches!(e, mir::ProjectionElem::Deref))
}

/// Whether the two-phase borrow reserved at `reserve` is active at
/// `location`, as rustc decides it.
fn is_active(
    body: &mir::Body<'_>,
    activation: TwoPhaseActivation,
    reserve: Location,
    location: Location,
) -> bool {
    let dominators = body.basic_blocks.dominators();
    let activation = match activation {
        TwoPhaseActivation::NotTwoPhase => return true,
        TwoPhaseActivation::NotActivated => return false,
        TwoPhaseActivation::ActivatedAt(loc) => loc,
    };
    if activation == location || activation.dominates(location, dominators) {
        return true;
    }
    !reserve
        .successor_within_block()
        .dominates(location, dominators)
}

fn any_maybe_uninit(
    move_data: &MoveData<'_>,
    is_uninit: &impl Fn(MovePathIndex) -> bool,
    mpi: MovePathIndex,
    deep: bool,
) -> bool {
    if is_uninit(mpi) {
        return true;
    }
    if !deep {
        return false;
    }
    let mut child = move_data.move_paths[mpi].first_child;
    while let Some(c) = child {
        if any_maybe_uninit(move_data, is_uninit, c, true) {
            return true;
        }
        child = move_data.move_paths[c].next_sibling;
    }
    false
}

/// The places of `pcg` with capabilities, sorted by their text.
fn capabilities<'a, 'tcx: 'a>(
    pcg: &Pcg<'a, 'tcx>,
    ctxt: CompilerCtxt<'a, 'tcx>,
) -> Vec<(Place<'tcx>, CapabilityKind)> {
    let mut caps = pcg
        .capabilities()
        .iter()
        .filter(|(place, _)| !place.contains_unsafe_deref(ctxt))
        .collect::<Vec<_>>();
    caps.sort_by_key(|(place, _)| place.display_string(ctxt));
    caps
}

/// The over-permission disagreements (and `w-live`) of every state of
/// `output`.
pub fn over_permission<'a, 'tcx: 'a>(
    output: &mut PcgOutput<'a, 'tcx>,
    bc: &'a dyn RustBorrowCheckerInterface<'tcx>,
) -> Vec<Disagreement> {
    let ctxt = output.ctxt();
    let facts = Facts::new(ctxt, bc);
    let body = facts.body;
    let mut storage = compute_fixpoint(
        MaybeStorageLive::new(Cow::Owned(always_storage_live_locals(body))),
        facts.tcx,
        body,
    )
    .into_results_cursor(body);
    let mut uninit_cursor = compute_fixpoint(
        MaybeUninitializedPlaces::new(facts.tcx, body, &facts.move_data),
        facts.tcx,
        body,
    )
    .into_results_cursor(body);
    let mut found = BTreeSet::new();
    for block in body.basic_blocks.indices() {
        if body[block].is_cleanup {
            continue;
        }
        let Ok(Some(bb)) = output.get_all_for_bb(block) else {
            continue;
        };
        let mut locations = bb
            .statements
            .iter()
            .map(|s| (s.location, s.states.clone()))
            .collect::<Vec<_>>();
        locations.push((
            Location {
                block,
                statement_index: body[block].statements.len(),
            },
            bb.terminator.states.clone(),
        ));
        for (location, states) in locations {
            let data = &body[block];
            let assigned = if location.statement_index < data.statements.len() {
                match &data.statements[location.statement_index].kind {
                    mir::StatementKind::Assign(assign) => Some(assign.0),
                    _ => None,
                }
            } else {
                match &data.terminator().kind {
                    mir::TerminatorKind::Call { destination, .. } => Some(*destination),
                    mir::TerminatorKind::Drop { place, .. } => Some(*place),
                    _ => None,
                }
            };
            let call_destination = match &data.terminator().kind {
                mir::TerminatorKind::Call { destination, .. }
                    if location.statement_index == data.statements.len() =>
                {
                    Some(*destination)
                }
                _ => None,
            };
            for phase in EvalStmtPhase::phases() {
                let after = phase == EvalStmtPhase::PostMain;
                let pcg = &states[phase];
                let point = format!("{location:?} {phase:?}");
                let in_scope = bc.borrows_in_scope_at(location, !after);
                if after {
                    uninit_cursor.seek_after_primary_effect(location);
                    storage.seek_after_primary_effect(location);
                } else {
                    uninit_cursor.seek_before_primary_effect(location);
                    storage.seek_before_primary_effect(location);
                }
                let uninit = uninit_cursor.get().clone();
                let storage_live = storage.get().clone();
                let live = facts.liveness.live(body, location, after);
                // The PCG activates a two-phase borrow in the pre-operands
                // phase of its use: in every phase of `location`, the
                // activations at `location` have happened, those at the
                // next location not.
                let activation_point = location.successor_within_block();
                for (place, capability) in capabilities(pcg, ctxt) {
                    let rp = place.to_rust_place(ctxt);
                    let shown = place.display_string(ctxt);
                    let mut report = |class: &'static str, detail: String| {
                        found.insert(Disagreement {
                            class,
                            place: shown.clone(),
                            point: point.clone(),
                            detail: format!("{capability:?}: {detail}"),
                        });
                    };
                    let (write, shallow) = match capability {
                        CapabilityKind::Exclusive => (true, false),
                        CapabilityKind::Read => (false, false),
                        CapabilityKind::Write | CapabilityKind::ShallowExclusive => (true, true),
                    };
                    for borrow in
                        facts.conflicting_loans(&in_scope, rp, write, shallow, activation_point)
                    {
                        if matches!(borrow.kind(), BorrowKind::Fake(_))
                            || facts.carriers(bc, borrow, &live).is_empty()
                        {
                            continue;
                        }
                        report(
                            "loan",
                            format!(
                                "rustc has a live loan of {:?} from {:?}",
                                borrow.borrowed_place(),
                                borrow.reserve_location()
                            ),
                        );
                    }
                    let is_destination = after
                        && call_destination
                            .is_some_and(|destination| destination.local == rp.local);
                    let deep = match capability {
                        CapabilityKind::Exclusive | CapabilityKind::Read => Some(true),
                        CapabilityKind::ShallowExclusive => Some(false),
                        CapabilityKind::Write => None,
                    };
                    if !is_destination
                        && let Some(deep) = deep
                        && facts.maybe_uninit(&uninit, rp, deep)
                    {
                        let dominators = body.basic_blocks.dominators();
                        let after_drop = body.basic_blocks.iter_enumerated().any(|(bb, data)| {
                            let drop = Location {
                                block: bb,
                                statement_index: data.statements.len(),
                            };
                            matches!(&data.terminator().kind, mir::TerminatorKind::Drop { place, .. } if place.local == rp.local)
                                && ((after && drop == location)
                                    || (drop != location && drop.dominates(location, dominators)))
                        });
                        report(
                            if after_drop {
                                "uninit-after-drop"
                            } else {
                                "uninit"
                            },
                            "rustc: maybe uninitialised".to_owned(),
                        );
                    }
                    if !storage_live.contains(rp.local) {
                        report("storage-dead", "rustc: storage maybe dead".to_owned());
                    }
                    if capability == CapabilityKind::Write
                        && matches!(phase, EvalStmtPhase::PreOperands | EvalStmtPhase::PostMain)
                        && live.contains(&rp.local)
                        && !assigned.is_some_and(|a| {
                            a.local == rp.local
                                && places_conflict(
                                    facts.tcx,
                                    body,
                                    a,
                                    rp,
                                    PlaceConflictBias::Overlap,
                                )
                        })
                        && !facts.maybe_uninit(&uninit, rp, true)
                    {
                        report(
                            "w-live",
                            "rustc: initialised, and the local is used later".to_owned(),
                        );
                    }
                }
            }
        }
    }
    found.into_iter().collect()
}

/// The over-restriction disagreements at block entries and after each
/// statement, and the probes that check them and the PCG's E and R claims
/// with rustc's borrow checker.
pub fn over_restriction<'a, 'tcx: 'a>(
    output: &mut PcgOutput<'a, 'tcx>,
    bc: &'a dyn RustBorrowCheckerInterface<'tcx>,
) -> (Vec<Disagreement>, Vec<Probe>) {
    let ctxt = output.ctxt();
    let rctxt = output.results_ctxt();
    let facts = Facts::new(ctxt, bc);
    let body = facts.body;
    let tcx = facts.tcx;
    let two_phase_temps: HashSet<mir::Local> = facts
        .borrow_set
        .iter()
        .filter(|b| !matches!(b.activation_location(), TwoPhaseActivation::NotTwoPhase))
        .map(|b| b.assigned_place().local)
        .collect();
    let mut found = BTreeSet::new();
    let mut probes = vec![];
    let mut seen = HashSet::new();
    let mut uninit_cursor = compute_fixpoint(
        MaybeUninitializedPlaces::new(tcx, body, &facts.move_data),
        tcx,
        body,
    )
    .into_results_cursor(body);
    for block in body.basic_blocks.indices() {
        if body[block].is_cleanup {
            continue;
        }
        let Ok(Some(bb)) = output.get_all_for_bb(block) else {
            continue;
        };
        output.cursor.seek_to_block_start(block);
        let Ok(entry) = output.cursor.get().expect_results_or_error() else {
            continue;
        };
        let entry = (*entry.data.pcg.entry_state).clone();
        // The state, where a probe is inserted, and the location after whose
        // primary effect rustc's facts hold (block entry: none).
        let mut snapshots = vec![(
            &entry,
            "entry".to_owned(),
            Location {
                block,
                statement_index: 0,
            },
            None,
        )];
        for statement in bb
            .statements
            .iter()
            .filter(|s| s.location.statement_index < body[block].statements.len())
        {
            snapshots.push((
                &statement.states[EvalStmtPhase::PostMain],
                format!("{:?} PostMain", statement.location),
                statement.location.successor_within_block(),
                Some(statement.location),
            ));
        }
        for (pcg, point, next, after) in snapshots {
            match after {
                None => uninit_cursor.seek_to_block_start(block),
                Some(location) => uninit_cursor.seek_after_primary_effect(location),
            }
            let uninit = uninit_cursor.get().clone();
            let in_scope = match after {
                None => bc.borrows_in_scope_at(next, true),
                Some(location) => bc.borrows_in_scope_at(location, false),
            };
            let live = facts.liveness.live(body, next, false);
            let mut places: HashSet<Place<'tcx>> = pcg
                .owned()
                .leaf_places(rctxt)
                .into_iter()
                .map(Into::into)
                .collect();
            places.extend(
                pcg.borrow_pcg()
                    .graph()
                    .places(ctxt)
                    .into_iter()
                    .filter(|p| pcg.is_expansion_leaf(*p, rctxt)),
            );
            places.extend(pcg.capabilities().iter().map(|(p, _)| p));
            let mut places = places
                .into_iter()
                .filter(|p| !p.contains_unsafe_deref(ctxt))
                .collect::<Vec<_>>();
            places.sort_by_key(|p| p.display_string(ctxt));
            for place in places {
                let capability = pcg.capabilities().get(place, rctxt);
                if capability == Some(CapabilityKind::ShallowExclusive) {
                    continue;
                }
                let rp = place.to_rust_place(ctxt);
                let Some(projection) = encode_projection(rp) else {
                    continue;
                };
                // A probe must not change what it measures: it must not
                // extend a reference's lifetime (every reference the place
                // holds or goes through is used later), a two-phase borrow's
                // temporary may be used only once, and an index local must be
                // initialised.
                if two_phase_temps.contains(&rp.local)
                    || !refs_live(bc, &live, body, tcx, rp)
                    || !rp.projection.iter().all(|e| match e {
                        mir::ProjectionElem::Index(l) => {
                            !facts.maybe_uninit(&uninit, l.into(), true)
                        }
                        _ => true,
                    })
                {
                    continue;
                }
                let mutable = place.is_mutable(LocalMutationIsAllowed::No, ctxt).is_ok()
                    && !behind_raw_or_shared(body, tcx, rp);
                let readable = !facts.maybe_uninit(&uninit, rp, true)
                    && facts
                        .conflicting_loans(&in_scope, rp, false, false, next)
                        .is_empty();
                let writable = readable
                    && mutable
                    && facts
                        .conflicting_loans(&in_scope, rp, true, false, next)
                        .is_empty();
                let probe = match capability {
                    Some(CapabilityKind::Read | CapabilityKind::Write) | None if writable => {
                        Some((true, "under-write"))
                    }
                    Some(CapabilityKind::Write) | None if readable => Some((false, "under-read")),
                    Some(CapabilityKind::Exclusive) => Some((mutable, "claim")),
                    Some(CapabilityKind::Read) => Some((false, "claim")),
                    _ => None,
                };
                let Some((mutable, class)) = probe else {
                    continue;
                };
                let shown = place.display_string(ctxt);
                let capability = capability.map_or("none".to_owned(), |c| format!("{c:?}"));
                if class != "claim" {
                    found.insert(Disagreement {
                        class,
                        place: shown.clone(),
                        point: point.clone(),
                        detail: format!(
                            "{capability}, but rustc allows {}",
                            if mutable { "&mut" } else { "&" }
                        ),
                    });
                }
                if seen.insert((next, rp, mutable)) {
                    probes.push(Probe {
                        block: next.block.as_usize(),
                        index: next.statement_index,
                        mutable,
                        local: rp.local.as_usize(),
                        projection,
                        class,
                        place: shown,
                        point: point.clone(),
                        capability,
                    });
                }
            }
        }
    }
    (found.into_iter().collect(), probes)
}

/// The projection of `place` as the probe injector of
/// `borrowck-body-storage` reads it: comma-separated `d` (deref), `f<i>`
/// (field), `v<i>` (variant), `i<local>` (index), `c<offset>:<min>:<end>`
/// (constant index), `s<from>:<to>:<end>` (subslice). `None` for other
/// projections.
#[must_use]
pub fn encode_projection(place: mir::Place<'_>) -> Option<String> {
    let mut parts = vec![];
    for elem in place.projection {
        parts.push(match elem {
            mir::ProjectionElem::Deref => "d".to_owned(),
            mir::ProjectionElem::Field(f, _) => format!("f{}", f.as_usize()),
            mir::ProjectionElem::Downcast(_, v) => format!("v{}", v.as_usize()),
            mir::ProjectionElem::Index(l) => format!("i{}", l.as_usize()),
            mir::ProjectionElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => format!("c{offset}:{min_length}:{}", u8::from(from_end)),
            mir::ProjectionElem::Subslice { from, to, from_end } => {
                format!("s{from}:{to}:{}", u8::from(from_end))
            }
            _ => return None,
        });
    }
    Some(parts.join(","))
}

fn behind_raw_or_shared<'tcx>(
    body: &mir::Body<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    place: mir::Place<'tcx>,
) -> bool {
    place.iter_projections().any(|(base, elem)| {
        matches!(elem, mir::ProjectionElem::Deref)
            && matches!(
                base.ty(body, tcx).ty.kind(),
                ty::TyKind::RawPtr(..) | ty::TyKind::Ref(_, _, ty::Mutability::Not)
            )
    })
}

/// Whether a borrow of `place` inserted where the locals `live` are used
/// later extends no reference's lifetime: a place that holds or goes through
/// a reference with a region that does not outlive the function's regions
/// must belong to a local used later.
fn refs_live<'tcx>(
    bc: &dyn RustBorrowCheckerInterface<'tcx>,
    live: &HashSet<mir::Local>,
    body: &mir::Body<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    place: mir::Place<'tcx>,
) -> bool {
    let universal: Vec<_> = bc
        .input_facts()
        .universal_region
        .iter()
        .map(|u| (*u).into())
        .collect();
    let local_regions = |t: ty::Ty<'tcx>| {
        let mut any = false;
        tcx.for_each_free_region(&t, |r| {
            if let ty::RegionKind::ReVar(vid) = r.kind()
                && !universal
                    .iter()
                    .any(|u| bc.region_infer_ctxt().eval_outlives(vid, *u))
            {
                any = true;
            }
        });
        any
    };
    let through_ref = place.iter_projections().any(|(base, elem)| {
        let base_ty = base.ty(body, tcx).ty;
        matches!(elem, mir::ProjectionElem::Deref) && base_ty.is_ref() && local_regions(base_ty)
    });
    if through_ref || local_regions(place.ty(body, tcx).ty) {
        return live.contains(&place.local);
    }
    true
}

/// Liveness of locals by real uses only: drops, `StorageDead` and cleanup
/// blocks do not count, so a local that is only dropped later is dead.
struct UseLiveness {
    live_out: Vec<HashSet<mir::Local>>,
}

fn use_effect(body: &mir::Body<'_>, location: Location, live: &mut HashSet<mir::Local>) {
    use crate::rustc_interface::middle::mir::visit::{
        MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor,
    };
    struct Uses {
        defs: Vec<mir::Local>,
        uses: Vec<mir::Local>,
    }
    impl<'tcx> Visitor<'tcx> for Uses {
        fn visit_place(&mut self, place: &mir::Place<'tcx>, context: PlaceContext, _: Location) {
            match context {
                PlaceContext::NonUse(_)
                | PlaceContext::MutatingUse(MutatingUseContext::Drop)
                | PlaceContext::NonMutatingUse(NonMutatingUseContext::Inspect) => {}
                PlaceContext::MutatingUse(
                    MutatingUseContext::Store
                    | MutatingUseContext::Call
                    | MutatingUseContext::AsmOutput,
                ) if place.projection.is_empty() => self.defs.push(place.local),
                _ => {
                    self.uses.push(place.local);
                    for elem in place.projection {
                        if let mir::ProjectionElem::Index(l) = elem {
                            self.uses.push(l);
                        }
                    }
                }
            }
        }
    }
    let mut uses = Uses {
        defs: vec![],
        uses: vec![],
    };
    let data = &body[location.block];
    if location.statement_index < data.statements.len() {
        uses.visit_statement(&data.statements[location.statement_index], location);
    } else {
        uses.visit_terminator(data.terminator(), location);
    }
    for def in uses.defs {
        live.remove(&def);
    }
    live.extend(uses.uses);
}

impl UseLiveness {
    fn new(body: &mir::Body<'_>) -> Self {
        let mut live_out = vec![HashSet::new(); body.basic_blocks.len()];
        let mut changed = true;
        while changed {
            changed = false;
            for (bb, data) in body.basic_blocks.iter_enumerated().rev() {
                if data.is_cleanup {
                    continue;
                }
                let mut out = HashSet::new();
                for succ in data.terminator().successors() {
                    if body[succ].is_cleanup {
                        continue;
                    }
                    let mut live = live_out[succ.index()].clone();
                    for i in (0..=body[succ].statements.len()).rev() {
                        use_effect(
                            body,
                            Location {
                                block: succ,
                                statement_index: i,
                            },
                            &mut live,
                        );
                    }
                    out.extend(live);
                }
                if out != live_out[bb.index()] {
                    live_out[bb.index()] = out;
                    changed = true;
                }
            }
        }
        Self { live_out }
    }

    /// The locals used after `location` (`after`) or from it on.
    fn live(&self, body: &mir::Body<'_>, location: Location, after: bool) -> HashSet<mir::Local> {
        let mut live = self.live_out[location.block.index()].clone();
        let last = body[location.block].statements.len();
        let stop = if after {
            location.statement_index + 1
        } else {
            location.statement_index
        };
        for i in (stop..=last).rev() {
            use_effect(
                body,
                Location {
                    block: location.block,
                    statement_index: i,
                },
                &mut live,
            );
        }
        live
    }
}
