use std::{cell::RefCell, rc::Rc};

use crate::{
    compute_fixpoint,
    rustc_interface::{
        dataflow::{Analysis, AnalysisEngine, with_cursor_state},
        middle::mir::{
            self,
            visit::{
                MutatingUseContext, NonMutatingUseContext, NonUseContext, PlaceContext, Visitor,
            },
        },
        mir_dataflow::{Backward, GenKill, JoinSemiLattice, ResultsCursor, fmt::DebugWithContext},
    },
    utils::{CompilerCtxt, Place, data_structures::HashSet},
};

#[derive(Clone, Eq, PartialEq, Debug)]
struct PlaceLivenessDomain<'tcx> {
    places: HashSet<Place<'tcx>>,
}

impl<'tcx> PlaceLivenessDomain<'tcx> {
    fn is_live(&self, place: Place<'tcx>) -> bool {
        self.places.iter().any(|p| p.conflicts_with(place))
    }
}

/// Which uses keep a place live.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Uses {
    /// All uses except the drop of a whole local. As for rustc's "regular
    /// uses" (`rustc_borrowck::def_use`), all the regions in the type of a
    /// local used in this sense must be live, and a drop of a part of a local
    /// is one. A drop of a whole local is different because the destructor
    /// may not use some of the regions (`#[may_dangle]`).
    Regular,
    /// All uses including drops, as in rustc's `MaybeLiveLocals`.
    RegularAndDrops,
}

struct TransferFunction<'a, 'tcx>(pub &'a mut PlaceLivenessDomain<'tcx>, Uses);

impl<'tcx> Visitor<'tcx> for TransferFunction<'_, 'tcx> {
    fn visit_place(
        &mut self,
        place: &mir::Place<'tcx>,
        context: PlaceContext,
        location: mir::Location,
    ) {
        if context == PlaceContext::MutatingUse(MutatingUseContext::Yield) {
            // The resume place is evaluated and assigned to only after coroutine resumes, so its
            // effect is handled separately in `call_resume_effect`.
            return;
        }

        match DefUse::for_place(*place, context, self.1) {
            Some(DefUse::Def) => {
                if let PlaceContext::MutatingUse(
                    MutatingUseContext::Call | MutatingUseContext::AsmOutput,
                ) = context
                {
                    // For the associated terminators, this is only a `Def` when the terminator
                    // returns "successfully." As such, we handle this case separately in
                    // `call_return_effect` above. However, if the place looks like `*_5`, this is
                    // still unconditionally a use of `_5`.
                } else {
                    self.0.kill((*place).into());
                }
            }
            Some(DefUse::Use) => self.0.gen_((*place).into()),
            None => {}
        }

        self.visit_projection(place.as_ref(), context, location);
    }

    fn visit_local(&mut self, local: mir::Local, context: PlaceContext, _: mir::Location) {
        DefUse::apply(self.0, local.into(), context, self.1);
    }
}

impl<'tcx> GenKill<Place<'tcx>> for PlaceLivenessDomain<'tcx> {
    fn gen_(&mut self, elem: Place<'tcx>) {
        self.places.retain(|p| !p.conflicts_with(elem));
        self.places.insert(elem);
    }

    fn kill(&mut self, elem: Place<'tcx>) {
        self.places.retain(|p| !p.conflicts_with(elem));
    }
}

impl JoinSemiLattice for PlaceLivenessDomain<'_> {
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for place in &other.places {
            changed |= self.places.insert(*place);
        }
        changed
    }
}

struct PlaceLivenessAnalysis(Uses);

impl<'tcx> Analysis<'tcx> for PlaceLivenessAnalysis {
    type Domain = PlaceLivenessDomain<'tcx>;
    type Direction = Backward;

    const NAME: &'static str = "place_liveness";

    fn bottom_value(&self, _body: &mir::Body<'tcx>) -> Self::Domain {
        PlaceLivenessDomain {
            places: HashSet::default(),
        }
    }

    fn initialize_start_block(&self, _body: &mir::Body<'tcx>, _state: &mut Self::Domain) {}

    fn apply_statement_effect(
        &self,
        state: &mut Self::Domain,
        statement: &mir::Statement<'tcx>,
        location: mir::Location,
    ) {
        TransferFunction(state, self.0).visit_statement(statement, location);
    }

    fn apply_terminator_effect(
        &self,
        state: &mut Self::Domain,
        terminator: &mir::Terminator<'tcx>,
        location: mir::Location,
    ) {
        TransferFunction(state, self.0).visit_terminator(terminator, location);
    }
}

type PlaceLivenessCursor<'mir, 'tcx> =
    Rc<RefCell<ResultsCursor<'mir, 'tcx, AnalysisEngine<PlaceLivenessAnalysis>>>>;

/// Place liveness analysis based on what currently exists in the compiler,
/// but field-sensitive. It distinguishes regular uses from drops in the same
/// way as rustc's borrow checker, so that the liveness of regions can follow
/// rustc's (see [`Uses`]).
#[derive(Clone)]
pub(crate) struct PlaceLiveness<'mir, 'tcx> {
    regular_uses: PlaceLivenessCursor<'mir, 'tcx>,
    regular_uses_and_drops: PlaceLivenessCursor<'mir, 'tcx>,
}

impl DebugWithContext<AnalysisEngine<PlaceLivenessAnalysis>> for PlaceLivenessDomain<'_> {}

impl<'mir, 'tcx> PlaceLiveness<'mir, 'tcx> {
    pub(crate) fn new<BC: Copy>(ctxt: CompilerCtxt<'mir, 'tcx, BC>) -> Self {
        let cursor = |uses| {
            Rc::new(RefCell::new(
                compute_fixpoint(
                    AnalysisEngine(PlaceLivenessAnalysis(uses)),
                    ctxt.tcx(),
                    ctxt.body(),
                )
                .into_results_cursor(ctxt.body()),
            ))
        };
        Self {
            regular_uses: cursor(Uses::Regular),
            regular_uses_and_drops: cursor(Uses::RegularAndDrops),
        }
    }

    /// Whether `place` may be used at `location` or later, other than by the
    /// drop of a whole local (see [`Uses::Regular`]).
    pub(crate) fn is_live(&self, place: Place<'tcx>, location: mir::Location) -> bool {
        Self::is_live_in(&self.regular_uses, place, location)
    }

    /// Whether `place` may be used or dropped at `location` or later.
    pub(crate) fn is_live_or_dropped_later(
        &self,
        place: Place<'tcx>,
        location: mir::Location,
    ) -> bool {
        Self::is_live_in(&self.regular_uses_and_drops, place, location)
    }

    fn is_live_in(
        cursor: &PlaceLivenessCursor<'mir, 'tcx>,
        place: Place<'tcx>,
        location: mir::Location,
    ) -> bool {
        let mut cursor = cursor.as_ref().borrow_mut();
        // Because this is a backwards analysis, seeking *after* the primary effect considers
        // the state *before* the statment at the location
        cursor.seek_after_primary_effect(location);
        with_cursor_state(&cursor, |state| state.is_live(place))
    }
}

#[derive(Eq, PartialEq, Clone)]
enum DefUse {
    Def,
    Use,
}

impl DefUse {
    fn apply<'tcx>(
        state: &mut PlaceLivenessDomain<'tcx>,
        place: mir::Place<'tcx>,
        context: PlaceContext,
        uses: Uses,
    ) {
        match DefUse::for_place(place, context, uses) {
            Some(DefUse::Def) => state.kill(place.into()),
            Some(DefUse::Use) => state.gen_(place.into()),
            None => {}
        }
    }

    #[allow(clippy::match_same_arms)]
    fn for_place(place: mir::Place<'_>, context: PlaceContext, uses: Uses) -> Option<DefUse> {
        #[rustversion::before(2026-08-12)]
        if matches!(
            context,
            PlaceContext::MutatingUse(MutatingUseContext::Retag)
        ) {
            return Some(DefUse::Use);
        }
        match context {
            PlaceContext::NonUse(NonUseContext::StorageDead) => Some(DefUse::Def),
            PlaceContext::NonUse(_) => None,
            // Like rustc, a drop of a part of a local is a regular use of it.
            PlaceContext::MutatingUse(MutatingUseContext::Drop) => {
                let is_use = uses == Uses::RegularAndDrops || !place.projection.is_empty();
                is_use.then_some(DefUse::Use)
            }

            PlaceContext::MutatingUse(
                MutatingUseContext::Call
                | MutatingUseContext::Yield
                | MutatingUseContext::AsmOutput
                | MutatingUseContext::Store,
            ) => {
                if place.is_indirect() {
                    // Treat derefs as a use of the base local. `*p = 4` is not a def of `p` but a
                    // use.
                    Some(DefUse::Use)
                } else if place.projection.is_empty() {
                    Some(DefUse::Def)
                } else {
                    None
                }
            }

            // Setting the discriminant is not a use because it does no reading, but it is also not
            // a def because it does not overwrite the whole place
            PlaceContext::MutatingUse(MutatingUseContext::SetDiscriminant) => {
                place.is_indirect().then_some(DefUse::Use)
            }

            // All other contexts are uses...
            PlaceContext::MutatingUse(
                MutatingUseContext::RawBorrow | MutatingUseContext::Borrow,
            )
            | PlaceContext::NonMutatingUse(
                NonMutatingUseContext::RawBorrow
                | NonMutatingUseContext::Copy
                | NonMutatingUseContext::Inspect
                | NonMutatingUseContext::Move
                | NonMutatingUseContext::PlaceMention
                | NonMutatingUseContext::FakeBorrow
                | NonMutatingUseContext::SharedBorrow,
            ) => Some(DefUse::Use),

            PlaceContext::MutatingUse(MutatingUseContext::Projection)
            | PlaceContext::NonMutatingUse(NonMutatingUseContext::Projection) => {
                unreachable!("A projection could be a def or a use and must be handled separately")
            }

            #[allow(unreachable_patterns)]
            _ => None,
        }
    }
}
