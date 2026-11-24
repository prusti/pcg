// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{borrow::Cow, collections::HashMap};

use derive_more::Deref;

use crate::{
    action::{AppliedActions, BorrowPcgAction, PcgActions},
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeRef},
        region_projection::PlaceOrConst,
    },
    error::PcgError,
    r#loop::{PlaceUsageType, PlaceUsages},
    pcg::{
        CapabilityKind, EvalStmtPhase, Pcg, PcgEngine, PcgNode, PcgSuccessor, ResultsCtxt,
        ctxt::HasSettings, place_capabilities::PlaceCapabilitiesReader, successor_blocks,
    },
    rustc_interface::{
        data_structures::fx::FxHashSet,
        dataflow::AnalysisEngine,
        index::IndexVec,
        middle::{
            mir::{self, BasicBlock, Body, Location},
            ty::TyCtxt,
        },
        mir_dataflow::ResultsCursor,
    },
    utils::{
        DebugCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, Place, display::DebugLines,
        domain_data::DomainDataStates, validity::HasValidityCheck,
    },
};

use crate::{
    borrow_pcg::action::actions::BorrowPcgActions,
    owned_pcg::RepackOp,
    utils::{CompilerCtxt, eval_stmt_data::EvalStmtData},
};

type Cursor<'mir, 'tcx, E> = ResultsCursor<'mir, 'tcx, E>;
/// The result of the PCG analysis.
pub struct PcgAnalysisResults<'a, 'tcx: 'a> {
    pub cursor: Cursor<'a, 'tcx, AnalysisEngine<PcgEngine<'a, 'tcx>>>,
    curr_stmt: Option<Location>,
    end_stmt: Option<Location>,
}

impl<'a, 'tcx: 'a> PcgAnalysisResults<'a, 'tcx> {
    pub(crate) fn new(cursor: Cursor<'a, 'tcx, AnalysisEngine<PcgEngine<'a, 'tcx>>>) -> Self {
        Self {
            cursor,
            curr_stmt: None,
            end_stmt: None,
        }
    }

    pub(crate) fn analysis_for_bb(&mut self, block: BasicBlock) {
        self.cursor.seek_to_block_start(block);
        let end_stmt = self.body().terminator_loc(block).successor_within_block();
        self.curr_stmt = Some(Location {
            block,
            statement_index: 0,
        });
        self.end_stmt = Some(end_stmt);
    }

    #[must_use]
    pub fn loop_place_usages(&self, loop_head: BasicBlock) -> Option<&PlaceUsages<'tcx>> {
        self.analysis()
            .body_analysis
            .loop_place_usage_analysis
            .get_used_places(loop_head)
    }

    fn body(&self) -> &'a Body<'tcx> {
        self.ctxt().body()
    }

    fn engine(&self) -> &PcgEngine<'a, 'tcx> {
        &self.cursor.analysis().0
    }

    pub fn results_ctxt(&self) -> ResultsCtxt<'a, 'tcx> {
        ResultsCtxt::new(
            self.engine().ctxt,
            self.engine().settings,
            self.engine().body_analysis,
        )
    }

    #[must_use]
    pub fn ctxt(&self) -> CompilerCtxt<'a, 'tcx> {
        self.engine().ctxt
    }

    /// Returns the free pcs for the location `exp_loc` and iterates the cursor
    /// to the *end* of that location.
    ///
    /// This function may return `None` if the PCG did not analyze this block.
    /// This could happen, for example, if the block would only be reached when unwinding from a panic.
    fn next(&mut self, exp_loc: Location) -> Result<Option<PcgLocation<'a, 'tcx>>, PcgError> {
        let location = self.curr_stmt.unwrap();
        assert_eq!(location, exp_loc);
        assert!(location < self.end_stmt.unwrap());

        self.cursor.seek_after_primary_effect(location);

        let state = self.cursor.get().expect_results_or_error()?;

        let result = PcgLocation {
            location,
            actions: state.data.actions.clone(),
            states: state.data.pcg.states.to_owned(),
        };

        self.curr_stmt = Some(location.successor_within_block());

        Ok(Some(result))
    }
    pub(crate) fn terminator<'slf>(&'slf mut self) -> Result<PcgTerminator<'a, 'tcx>, PcgError> {
        let location = self.curr_stmt.unwrap();
        assert_eq!(location, self.end_stmt.unwrap());
        self.curr_stmt = None;
        self.end_stmt = None;

        let state = self.cursor.get().expect_results_or_error()?;
        let from_pcg = &state.data.pcg;
        let from_post_main = from_pcg.states[EvalStmtPhase::PostMain].clone();
        let states = state.data.pcg.states.to_owned();
        let self_abstraction_edges = from_post_main
            .borrow
            .graph()
            .abstraction_edges()
            .collect::<FxHashSet<_>>();

        let ctxt: ResultsCtxt<'a, 'tcx> = self.results_ctxt();
        let block = &self.body()[location.block];

        let succ_blocks = successor_blocks(block.terminator())
            .into_iter()
            .filter(|succ| {
                self.cursor
                    .analysis()
                    .0
                    .reachable_blocks
                    .borrow()
                    .contains(succ.index())
            })
            .collect::<Vec<_>>();
        let succs = succ_blocks
            .into_iter()
            .map(|succ| {
                self.cursor.seek_to_block_start(succ);
                let to = self
                    .cursor
                    .get()
                    .expect_results_or_error()?
                    .data
                    .pcg
                    .clone();

                let mut actions =
                    from_post_main.bridge(&to.entry_state, location.block, succ, ctxt)?;

                let mut borrow_actions = BorrowPcgActions::new();
                for abstraction in to.entry_state.borrow.graph().abstraction_edges() {
                    if !self_abstraction_edges.contains(&abstraction) {
                        borrow_actions.push(
                            BorrowPcgAction::add_edge(
                                BorrowPcgEdge::new(
                                    abstraction.value.clone().into(),
                                    abstraction.conditions,
                                ),
                                "terminator",
                            ),
                            self.engine(),
                        );
                    }
                }

                actions.extend(borrow_actions.into());

                Ok(PcgSuccessor::new(
                    succ,
                    actions,
                    to.entry_state.borrow.clone().into(),
                ))
            })
            .collect::<Result<Vec<_>, PcgError>>()?;
        Ok(PcgTerminator { succs, states })
    }

    /// Obtains the results of the dataflow analysis for all blocks.
    ///
    /// This is rather expensive to compute and may take a lot of memory. You
    /// may want to consider using `get_all_for_bb` instead.
    pub fn results_for_all_blocks(&mut self) -> Result<PcgBasicBlocks<'a, 'tcx>, PcgError> {
        let mut result = IndexVec::new();
        for block in self.body().basic_blocks.indices() {
            let pcg_block = self.get_all_for_bb(block)?;
            result.push(pcg_block);
        }
        Ok(PcgBasicBlocks(result))
    }

    #[must_use]
    pub fn analysis(&self) -> &PcgEngine<'a, 'tcx> {
        &self.cursor.analysis().0
    }

    #[must_use]
    pub fn first_error(&self) -> Option<PcgError> {
        self.analysis().first_error.borrow().error().cloned()
    }

    /// Recommended interface.
    /// Does *not* require that one calls `analysis_for_bb` first
    /// This function may return `None` if the PCG did not analyze this block.
    /// This could happen, for example, if the block would only be reached when unwinding from a panic.
    pub fn get_all_for_bb<'slf>(
        &'slf mut self,
        block: BasicBlock,
    ) -> Result<Option<PcgBasicBlock<'a, 'tcx>>, PcgError> {
        let mut statements: Vec<PcgLocation<'a, 'tcx>> = Vec::new();
        if !self.for_each_statement_in_bb(block, |stmt| statements.push(stmt))? {
            return Ok(None);
        }
        let terminator = self.terminator()?;
        Ok(Some(PcgBasicBlock {
            statements,
            terminator,
            block,
        }))
    }

    /// Passes the results of each statement of `block` (not its terminator),
    /// in order, to `f`, so that the caller need not hold the results of the
    /// whole block at once. Returns `false` if the PCG did not analyze `block`.
    /// On an error, `f` has seen the statements before the failing one.
    pub(crate) fn for_each_statement_in_bb(
        &mut self,
        block: BasicBlock,
        mut f: impl FnMut(PcgLocation<'a, 'tcx>),
    ) -> Result<bool, PcgError> {
        if !self
            .analysis()
            .reachable_blocks
            .borrow()
            .contains(block.index())
        {
            return Ok(false);
        }
        self.analysis_for_bb(block);
        let end_stmt = self.end_stmt.unwrap();
        while self.curr_stmt.unwrap() != end_stmt {
            let Some(stmt) = self.next(self.curr_stmt.unwrap())? else {
                return Ok(false);
            };
            f(stmt);
        }
        Ok(true)
    }
}

/// The results of the PCG analysis for all basic blocks.
#[derive(Deref)]
pub struct PcgBasicBlocks<'a, 'tcx>(IndexVec<BasicBlock, Option<PcgBasicBlock<'a, 'tcx>>>);

impl<'tcx> PcgBasicBlocks<'_, 'tcx> {
    #[must_use]
    pub fn get_statement(&self, location: Location) -> Option<&PcgLocation<'_, 'tcx>> {
        if let Some(pcg_block) = &self.0[location.block] {
            pcg_block.statements.get(location.statement_index)
        } else {
            None
        }
    }

    fn aggregate<T: std::hash::Hash + Eq>(
        &self,
        f: impl Fn(&PcgLocation<'_, 'tcx>) -> FxHashSet<T>,
    ) -> FxHashSet<T> {
        let mut result = FxHashSet::default();
        for block in &self.0 {
            if let Some(pcg_block) = &block {
                for stmt in &pcg_block.statements {
                    result.extend(f(stmt));
                }
            }
        }
        result
    }

    #[must_use]
    pub fn all_place_aliases<'mir>(
        &self,
        place: mir::Place<'tcx>,
        body: &'mir Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> FxHashSet<mir::Place<'tcx>> {
        self.aggregate(|stmt| stmt.aliases(place, body, tcx))
    }
}

/// The results of the PCG analysis for a basic block.
pub struct PcgBasicBlock<'a, 'tcx> {
    pub statements: Vec<PcgLocation<'a, 'tcx>>,
    pub terminator: PcgTerminator<'a, 'tcx>,
    pub(crate) block: BasicBlock,
}

impl<'a, 'tcx: 'a> PcgBasicBlock<'a, 'tcx> {
    pub(crate) fn statements(&self) -> impl Iterator<Item = &PcgLocation<'a, 'tcx>> {
        self.statements.iter()
    }

    pub(crate) fn successors(&self) -> impl Iterator<Item = &PcgSuccessor<'a, 'tcx>> {
        self.terminator.succs.iter()
    }

    /// The capabilities that the loop with this block as its head requires of
    /// the places that hold its `place_usages` at the head.
    ///
    /// A usage is held by the place itself or its nearest ancestor with a
    /// capability at the head; if the place is unpacked at the head, by the
    /// places it is unpacked into. The capability of a holder is the minimum
    /// of its capability at the head and the loop's usage of it, or the usage
    /// if the two are incomparable: e.g. a mutable reference whose target is
    /// unpacked (`ShallowExclusive`) and whose own value the loop only reads
    /// is reported at `R`.
    ///
    /// A usage behind a mutable reference in its holder uses the place behind
    /// the reference rather than the holder's own value. If the loop does not
    /// write the holder's own value, the holder is reported at `R` and the
    /// place behind the first such reference on the usage's path (e.g. `*x`
    /// for a holder `x`, or `*s.r` for a holder `s`) is reported separately,
    /// with the capability of its usages limited by the holder's, although
    /// the holder is not unpacked to it at the head. If the loop writes the
    /// holder's own value, the holder's capability also covers the places
    /// behind it.
    ///
    /// Each reference with a capability at the head on the path to a reported
    /// place is reported as well, separately from the places behind it: at
    /// `R` if the loop does not use the reference itself, since the loop then
    /// only reads it to reach the places behind it.
    ///
    /// A place is listed after the places it extends, through which it is
    /// reached.
    pub fn loop_invariant_place_capabilities<'c>(
        &self,
        place_usages: &PlaceUsages<'tcx>,
        ctxt: impl HasCompilerCtxt<'c, 'tcx>,
    ) -> Vec<(Place<'tcx>, CapabilityKind)>
    where
        'tcx: 'c,
    {
        /// The loop's usages held by one place: of the place's own value, and
        /// of the places behind the mutable references in it. Multiple usages
        /// can resolve to the same place; their requirements are joined before
        /// limiting the capability to what is available at the head.
        #[derive(Default)]
        struct HolderUsages<'tcx> {
            own: Option<PlaceUsageType>,
            behind: HashMap<Place<'tcx>, PlaceUsageType>,
        }

        let initial_capabilities =
            self.statements[0].states[EvalStmtPhase::PreOperands].capabilities();
        let mut usages: HashMap<Place<'tcx>, HolderUsages<'tcx>> = HashMap::default();
        for place_usage in place_usages.iter() {
            let holder = std::iter::successors(Some(place_usage.place), |p| p.parent_place())
                .find(|place| initial_capabilities.get(*place, ctxt).is_some());
            let holders = match holder {
                Some(holder) => vec![holder],
                None => initial_capabilities
                    .iter()
                    .map(|(place, _)| place)
                    .filter(|place| place_usage.place.is_strict_prefix_of(*place))
                    .collect(),
            };
            let usage = place_usage.usage;
            for holder in holders {
                let holder_usages = usages.entry(holder).or_default();
                match place_usage.place.first_mut_deref_after(holder, ctxt) {
                    Some(behind) => {
                        holder_usages
                            .behind
                            .entry(behind)
                            .and_modify(|existing| *existing = existing.joined(usage))
                            .or_insert(usage);
                    }
                    None => {
                        holder_usages.own =
                            Some(holder_usages.own.map_or(usage, |own| own.joined(usage)));
                    }
                }
            }
        }
        let capability_of = |holder: Place<'tcx>, usage: PlaceUsageType| {
            let usage_capability = match usage {
                PlaceUsageType::Read => CapabilityKind::Read,
                PlaceUsageType::Write => CapabilityKind::Write,
                PlaceUsageType::Exclusive => CapabilityKind::Exclusive,
            };
            initial_capabilities
                .get(holder, ctxt)
                .expect("a holder has a capability at the head")
                .minimum(usage_capability)
                .unwrap_or(usage_capability)
        };
        let mut capabilities: HashMap<Place<'tcx>, CapabilityKind> = HashMap::default();
        for (holder, HolderUsages { own, behind }) in usages {
            if own.is_none_or(PlaceUsageType::is_read) && !behind.is_empty() {
                capabilities.insert(holder, capability_of(holder, PlaceUsageType::Read));
                for (place, usage) in behind {
                    capabilities.insert(place, capability_of(holder, usage));
                }
            } else {
                let usage = behind
                    .into_values()
                    .chain(own)
                    .reduce(PlaceUsageType::joined)
                    .expect("a holder holds a usage");
                capabilities.insert(holder, capability_of(holder, usage));
            }
        }
        let references_on_paths = capabilities
            .keys()
            .flat_map(|place| std::iter::successors(place.parent_place(), |p| p.parent_place()))
            .filter(|place| {
                place.is_ref(ctxt)
                    && initial_capabilities.get(*place, ctxt).is_some()
                    && !capabilities.contains_key(place)
            })
            .collect::<Vec<_>>();
        for reference in references_on_paths {
            capabilities.insert(reference, CapabilityKind::Read);
        }
        let mut capabilities = capabilities.into_iter().collect::<Vec<_>>();
        capabilities.sort_by_key(|(place, _)| place.projection.len());
        capabilities
    }

    #[must_use]
    pub fn debug_lines<Ctxt: HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>>(
        &self,
        ctxt: Ctxt,
    ) -> Vec<Cow<'static, str>> {
        let mut result = Vec::new();
        for stmt in &self.statements {
            for phase in EvalStmtPhase::phases() {
                for line in stmt.debug_lines(phase, ctxt) {
                    result.push(format!("{:?} {}: {}", stmt.location, phase, line).into());
                }
            }
        }
        for term_succ in &self.terminator.succs {
            for line in term_succ.debug_lines(ctxt) {
                result
                    .push(format!("{:?} -> {:?}: {}", self.block, term_succ.block(), line).into());
            }
        }
        result
    }
}

/// The PCG state at a MIR location. Also contains associated actions performed
/// when analysing the statement at that location.
#[derive(Debug, Clone)]
pub struct PcgLocation<'a, 'tcx> {
    pub location: Location,
    pub states: DomainDataStates<Pcg<'a, 'tcx>>,
    pub(crate) actions: EvalStmtData<AppliedActions<'tcx>>,
}

impl<Ctxt> DebugLines<Ctxt> for Vec<RepackOp<'_>> {
    fn debug_lines(&self, _ctxt: Ctxt) -> Vec<Cow<'static, str>> {
        self.iter().map(|r| Cow::Owned(format!("{r:?}"))).collect()
    }
}

impl<'a, 'tcx: 'a, Ctxt: DebugCtxt + HasSettings<'a> + HasBorrowCheckerCtxt<'a, 'tcx>>
    HasValidityCheck<Ctxt> for PcgLocation<'a, 'tcx>
{
    fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
        // TODO
        self.states.check_validity(ctxt)
    }
}

impl<'a, 'tcx: 'a> PcgLocation<'a, 'tcx> {
    #[must_use]
    pub fn actions<'slf>(&'slf self, phase: EvalStmtPhase) -> PcgActions<'tcx> {
        self.actions[phase].map_actions(|action| action.action.clone())
    }

    #[must_use]
    pub fn ancestor_edges<'slf, 'mir: 'slf, 'bc: 'slf>(
        &'slf self,
        place: Place<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> FxHashSet<BorrowPcgEdgeRef<'tcx, 'slf>> {
        let borrows_graph = self.states[EvalStmtPhase::PostMain].borrow.graph();
        let mut ancestors = borrows_graph.ancestor_edges(place.into(), ctxt);
        for rp in place.lifetime_projections(ctxt) {
            ancestors.extend(borrows_graph.ancestor_edges(rp.into(), ctxt));
        }
        ancestors
    }

    pub fn aliases<'mir>(
        &self,
        place: impl Into<Place<'tcx>>,
        body: &'mir Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> FxHashSet<mir::Place<'tcx>> {
        let place: Place<'tcx> = place.into();
        let ctxt = CompilerCtxt::new(body, tcx, ());
        self.states[EvalStmtPhase::PostMain]
            .borrow
            .graph()
            .aliases(place.into(), ctxt)
            .into_iter()
            .filter_map(|p| match p {
                PcgNode::Place(p) => p.as_current_place(),
                PcgNode::LifetimeProjection(p) => match p.base() {
                    PlaceOrConst::Place(p) => {
                        let assoc_place = p.related_local_place();
                        assoc_place
                            .is_ref(ctxt)
                            .then(|| assoc_place.project_deref(ctxt))
                    }
                    _ => None,
                },
            })
            .map(|p| p.to_rust_place(ctxt))
            .collect()
    }

    pub(crate) fn debug_lines<Ctxt: HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>>(
        &self,
        phase: EvalStmtPhase,
        ctxt: Ctxt,
    ) -> Vec<Cow<'static, str>> {
        let mut result = self.states[phase].debug_lines(ctxt);
        for action in self.actions[phase].iter() {
            result.push(action.action.debug_line(ctxt));
        }
        result
    }
}

#[derive(Debug)]
pub struct PcgTerminator<'a, 'tcx> {
    pub succs: Vec<PcgSuccessor<'a, 'tcx>>,
    pub(crate) states: DomainDataStates<Pcg<'a, 'tcx>>,
}
