//! Loop Analysis Utilities
//!
// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

mod loop_set;

use derive_more::{Deref, DerefMut};
use itertools::Itertools;

#[cfg(feature = "visualization")]
use crate::visualization::stmt_graphs;

use crate::{
    compute_fixpoint,
    r#loop::loop_set::LoopSet,
    rustc_interface::{
        dataflow::{Analysis, AnalysisEngine},
        index::{Idx, IndexVec},
        middle::{
            mir::{
                self, BasicBlock, Body, START_BLOCK,
                visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext},
            },
            ty,
        },
        mir_dataflow::{Forward, JoinSemiLattice, fmt::DebugWithContext},
    },
    utils::{
        HasCompilerCtxt, Place,
        data_structures::HashMap,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        visitor::FallableVisitor,
    },
    validity_checks_enabled,
};

#[derive(Clone, Debug)]
pub struct LoopAnalysis {
    /// Tracks the loops that each basic block is in.
    bb_data: IndexVec<BasicBlock, LoopSet>,
    /// Identifies the head of each loop.
    loop_heads: IndexVec<LoopId, BasicBlock>,
}

impl LoopAnalysis {
    #[must_use]
    pub fn find_loops(body: &Body) -> Self {
        let successors: IndexVec<BasicBlock, Vec<BasicBlock>> = IndexVec::from_fn_n(
            |bb: BasicBlock| body.basic_blocks[bb].terminator().successors().collect(),
            body.basic_blocks.len(),
        );
        let predecessors: IndexVec<BasicBlock, Vec<BasicBlock>> = IndexVec::from_fn_n(
            |bb: BasicBlock| {
                body.basic_blocks.predecessors()[bb]
                    .iter()
                    .copied()
                    .collect()
            },
            body.basic_blocks.len(),
        );
        let dominators = body.basic_blocks.dominators();
        Self::find_loops_in_cfg(
            body.basic_blocks.len(),
            body.basic_blocks.reverse_postorder().iter().copied().rev(),
            &successors,
            &predecessors,
            |from, to| dominators.dominates(to, from),
        )
    }

    fn find_loops_in_cfg(
        block_count: usize,
        backedge_search_order: impl IntoIterator<Item = BasicBlock>,
        successors: &IndexVec<BasicBlock, Vec<BasicBlock>>,
        predecessors: &IndexVec<BasicBlock, Vec<BasicBlock>>,
        is_backedge: impl Fn(BasicBlock, BasicBlock) -> bool,
    ) -> Self {
        let mut analysis = LoopAnalysis {
            bb_data: IndexVec::from_elem_n(LoopSet::new(), block_count),
            loop_heads: IndexVec::new(),
        };

        let mut loop_head_bb_index: IndexVec<BasicBlock, LoopId> =
            IndexVec::from_elem_n(NO_LOOP, block_count);
        for bb in backedge_search_order {
            for &succ in &successors[bb] {
                if is_backedge(bb, succ) {
                    let loop_idx = &mut loop_head_bb_index[succ];
                    if *loop_idx == NO_LOOP {
                        *loop_idx = LoopId::new(analysis.loop_heads.len());
                        analysis.loop_heads.push(succ);
                    }
                    analysis.add_natural_loop(succ, bb, *loop_idx, predecessors);
                }
            }
        }
        if validity_checks_enabled() {
            analysis.consistency_check();
        }
        analysis
    }

    fn add_natural_loop(
        &mut self,
        head: BasicBlock,
        tail: BasicBlock,
        loop_idx: LoopId,
        predecessors: &IndexVec<BasicBlock, Vec<BasicBlock>>,
    ) {
        self.bb_data[head].add(loop_idx);
        let mut stack = vec![tail];
        while let Some(bb) = stack.pop() {
            if self.bb_data[bb].contains(loop_idx) {
                continue;
            }
            self.bb_data[bb].add(loop_idx);
            stack.extend(predecessors[bb].iter().copied());
        }
    }

    #[must_use]
    pub fn in_loop(&self, bb: BasicBlock, l: LoopId) -> bool {
        self.bb_data[bb].contains(l)
    }

    /// Returns an iterator over the loops that `bb` is in.
    pub fn loops(&self, bb: BasicBlock) -> impl DoubleEndedIterator<Item = LoopId> + '_ {
        self.bb_data[bb].iter()
    }

    /// Returns an iterator over all loops in the body.
    pub fn all_loops(&self) -> impl DoubleEndedIterator<Item = LoopId> + '_ {
        self.loop_heads.iter_enumerated().map(|(idx, _)| idx)
    }

    /// Returns the number of loops that `bb` is in.
    #[must_use]
    pub fn loop_depth(&self, bb: BasicBlock) -> usize {
        self.loops(bb).count()
    }
    #[must_use]
    pub fn loop_nest_depth(&self, l: LoopId) -> usize {
        self.loop_depth(self[l]) - 1
    }
    /// Returns the loop which contains `bb` as well as all other loops of `bb`.
    #[must_use]
    pub fn outermost_loop(&self, bb: BasicBlock) -> Option<LoopId> {
        self.loops(bb).min_by_key(|l| self.loop_nest_depth(*l))
    }
    /// Returns the loop which contains `bb` but no other loops of `bb`.
    #[must_use]
    pub fn innermost_loop(&self, bb: BasicBlock) -> Option<LoopId> {
        self.loops(bb).max_by_key(|l| self.loop_nest_depth(*l))
    }

    /// If `bb` is a loop head, return the loop for which it is the head.
    #[must_use]
    pub fn loop_head_of(&self, bb: BasicBlock) -> Option<LoopId> {
        self.loops(bb).find(|l| self[*l] == bb)
    }

    pub(crate) fn loop_head_block(&self, loop_id: LoopId) -> BasicBlock {
        self.loop_heads[loop_id]
    }

    fn consistency_check(&self) {
        // Start block can be in a maximum of one loop, of which it is the head
        let mut start_loops: Vec<_> = self.loops(START_BLOCK).collect();
        if let Some(l) = start_loops.pop() {
            assert_eq!(self[l], START_BLOCK);
        }
        assert!(
            start_loops.is_empty(),
            "start block is in more than one loop: {start_loops:?}"
        );
        // A bb can only be the loop head of a single loop
        for lh in &self.loop_heads {
            assert_eq!(
                self.loop_heads.iter().filter(|other| *other == lh).count(),
                1
            );
        }
    }
}

impl std::ops::Index<LoopId> for LoopAnalysis {
    type Output = BasicBlock;
    fn index(&self, index: LoopId) -> &Self::Output {
        &self.loop_heads[index]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct LoopId(usize);
impl Idx for LoopId {
    fn new(idx: usize) -> Self {
        Self(idx)
    }
    fn index(self) -> usize {
        self.0
    }
}
const NO_LOOP: LoopId = LoopId(usize::MAX);

#[cfg(test)]
mod tests {
    use super::*;

    fn block(index: usize) -> BasicBlock {
        BasicBlock::new(index)
    }

    fn make_cfg(
        successor_indices: &[Vec<usize>],
    ) -> (
        IndexVec<BasicBlock, Vec<BasicBlock>>,
        IndexVec<BasicBlock, Vec<BasicBlock>>,
    ) {
        let successors: IndexVec<BasicBlock, Vec<BasicBlock>> = IndexVec::from_fn_n(
            |bb: BasicBlock| {
                successor_indices[bb.index()]
                    .iter()
                    .copied()
                    .map(block)
                    .collect()
            },
            successor_indices.len(),
        );
        let mut predecessors: IndexVec<BasicBlock, Vec<BasicBlock>> =
            IndexVec::from_elem_n(Vec::new(), successor_indices.len());
        for (bb, successors) in successors.iter_enumerated() {
            for &successor in successors {
                predecessors[successor].push(bb);
            }
        }
        (successors, predecessors)
    }

    #[test]
    fn nested_loop_membership_includes_inner_body_in_outer_loop() {
        let (successors, predecessors) = make_cfg(&[
            vec![1],
            vec![2],
            vec![3],
            vec![4, 5],
            vec![],
            vec![6],
            vec![7],
            vec![8],
            vec![9],
            vec![10],
            vec![11],
            vec![12],
            vec![13, 14],
            vec![1],
            vec![15],
            vec![16],
            vec![17],
            vec![18],
            vec![10],
        ]);

        let analysis = LoopAnalysis::find_loops_in_cfg(
            successors.len(),
            (0..successors.len()).rev().map(block),
            &successors,
            &predecessors,
            |from, to| matches!((from.index(), to.index()), (13, 1) | (18, 10)),
        );
        let outer = analysis.loop_head_of(block(1)).unwrap();
        let inner = analysis.loop_head_of(block(10)).unwrap();

        for index in 14..=18 {
            assert!(analysis.in_loop(block(index), outer));
            assert!(analysis.in_loop(block(index), inner));
        }
    }
}

#[cfg(test)]
mod place_usage_tests {
    use super::*;
    use crate::rustc_interface::middle::mir::{Local, ProjectionElem};

    /// A projection element that is disjoint from `index(other)` for any other
    /// offset, and that (unlike a field projection) does not carry a type.
    const fn index(offset: u64) -> mir::PlaceElem<'static> {
        ProjectionElem::ConstantIndex {
            offset,
            min_length: 2,
            from_end: false,
        }
    }

    const FIRST: &[mir::PlaceElem<'static>] = &[index(0)];
    const SECOND: &[mir::PlaceElem<'static>] = &[index(1)];
    const FIRST_FIRST: &[mir::PlaceElem<'static>] = &[index(0), index(0)];

    fn place(projection: &'static [mir::PlaceElem<'static>]) -> Place<'static> {
        Place::new(Local::from_u32(1), projection)
    }

    fn usages(usages: &[(Place<'static>, PlaceUsageType)]) -> PlaceUsages<'static> {
        usages
            .iter()
            .map(|(place, usage)| PlaceUsage {
                place: *place,
                usage: *usage,
            })
            .collect()
    }

    #[test]
    fn read_and_write_join_to_exclusive() {
        assert_eq!(
            PlaceUsageType::Read.joined(PlaceUsageType::Write),
            PlaceUsageType::Exclusive
        );
        assert_eq!(
            PlaceUsageType::Read.joined(PlaceUsageType::Read),
            PlaceUsageType::Read
        );
        assert_eq!(
            PlaceUsageType::Write.joined(PlaceUsageType::Write),
            PlaceUsageType::Write
        );
        assert_eq!(
            PlaceUsageType::Exclusive.joined(PlaceUsageType::Read),
            PlaceUsageType::Exclusive
        );
    }

    #[test]
    fn consolidate_merges_overlapping_places() {
        let consolidated = usages(&[
            (place(FIRST), PlaceUsageType::Read),
            (place(FIRST_FIRST), PlaceUsageType::Write),
        ])
        .consolidate();
        assert_eq!(
            consolidated,
            usages(&[(place(FIRST), PlaceUsageType::Exclusive)])
        );
    }

    #[test]
    fn consolidate_keeps_disjoint_places_apart() {
        let original = usages(&[
            (place(FIRST), PlaceUsageType::Write),
            (place(SECOND), PlaceUsageType::Read),
        ]);
        assert_eq!(original.consolidate(), original);
    }

    #[test]
    fn consolidated_places_are_pairwise_disjoint() {
        let consolidated = usages(&[
            (place(FIRST_FIRST), PlaceUsageType::Read),
            (place(SECOND), PlaceUsageType::Read),
            (place(FIRST), PlaceUsageType::Write),
        ])
        .consolidate();
        let places = consolidated.iter_places().collect::<Vec<_>>();
        for (idx, p) in places.iter().enumerate() {
            for other in &places[idx + 1..] {
                assert!(!p.is_prefix_of(*other) && !other.is_prefix_of(*p));
            }
        }
        assert_eq!(places.len(), 2);
    }

    #[test]
    fn unpack_order_puts_read_only_places_last() {
        let order = usages(&[
            (place(FIRST), PlaceUsageType::Read),
            (place(SECOND), PlaceUsageType::Write),
        ])
        .loop_head_unpack_order();
        assert_eq!(
            order.iter().map(|usage| usage.usage).collect::<Vec<_>>(),
            vec![PlaceUsageType::Write, PlaceUsageType::Read]
        );
    }
}

#[derive(Clone, Debug, Deref, DerefMut, PartialEq, Eq)]
struct LoopPlaceUsageDomain<'tcx> {
    used_places: PlaceUsages<'tcx>,
}

impl JoinSemiLattice for PlaceUsages<'_> {
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for other_place_usage in other.iter() {
            changed |= self.update(other_place_usage.place, other_place_usage.usage);
        }
        changed
    }
}

impl JoinSemiLattice for LoopPlaceUsageDomain<'_> {
    fn join(&mut self, other: &Self) -> bool {
        self.used_places.join(&other.used_places)
    }
}

/// The way in which a place is used inside a loop.
///
/// These are the usage types $M = \{R, W, E\}$ of the loop invariant
/// capability calculation. `Exclusive` is the top element of the
/// meet-semilattice; `Read` and `Write` are incomparable, and their join is
/// `Exclusive`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, serde_derive::Serialize)]
#[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "type-export", ts(export))]
pub enum PlaceUsageType {
    /// The place is read from.
    Read,
    /// The place is assigned to.
    Write,
    /// The place is moved out of or mutably borrowed.
    Exclusive,
}

impl PlaceUsageType {
    /// The join of two usage types in the meet-semilattice described above.
    #[must_use]
    pub(crate) fn joined(self, other: Self) -> Self {
        match (self, other) {
            (PlaceUsageType::Read, PlaceUsageType::Read) => PlaceUsageType::Read,
            (PlaceUsageType::Write, PlaceUsageType::Write) => PlaceUsageType::Write,
            _ => PlaceUsageType::Exclusive,
        }
    }

    #[must_use]
    pub(crate) fn is_read(self) -> bool {
        matches!(self, PlaceUsageType::Read)
    }
}

impl JoinSemiLattice for PlaceUsageType {
    fn join(&mut self, other: &Self) -> bool {
        let joined = self.joined(*other);
        let changed = joined != *self;
        *self = joined;
        changed
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct PlaceUsage<'tcx> {
    pub(crate) place: Place<'tcx>,
    pub(crate) usage: PlaceUsageType,
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt> for PlaceUsage<'tcx> {
    fn display_output(&self, ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(format!("{}: {:?}", self.place.display_string(ctxt), self.usage).into())
    }
}

#[derive(Clone, Debug, Deref, PartialEq, Eq, Default)]
pub struct PlaceUsages<'tcx>(HashMap<Place<'tcx>, PlaceUsageType>);

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt> for PlaceUsages<'tcx> {
    fn display_output(&self, ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(
            self.0
                .iter()
                .map(|(p, usage)| format!("{}: {:?}", p.display_string(ctxt), usage))
                .join("\n")
                .into(),
        )
    }
}

impl<'tcx> PlaceUsages<'tcx> {
    pub(crate) fn iter_places(&self) -> impl Iterator<Item = Place<'tcx>> + '_ {
        self.0.keys().copied()
    }

    pub(crate) fn contains(&self, place: Place<'tcx>) -> bool {
        self.0.contains_key(&place)
    }

    pub(crate) fn joined_with(&self, other: &Self) -> Self {
        let mut clone = self.clone();
        clone.join(other);
        clone
    }

    pub(crate) fn usages_where(
        &self,
        predicate: impl Fn(PlaceUsage<'tcx>) -> bool,
    ) -> PlaceUsages<'tcx> {
        let mut clone = self.clone();
        clone.0.retain(|p, usage| {
            predicate(PlaceUsage {
                place: *p,
                usage: *usage,
            })
        });
        clone
    }

    #[must_use]
    fn update(&mut self, place: Place<'tcx>, usage: PlaceUsageType) -> bool {
        if let Some(existing_usage) = self.0.get(&place) {
            let joined = existing_usage.joined(usage);
            if joined == *existing_usage {
                false
            } else {
                self.0.insert(place, joined);
                true
            }
        } else {
            self.0.insert(place, usage);
            true
        }
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = PlaceUsage<'tcx>> + '_ {
        self.0.iter().map(|(p, usage)| PlaceUsage {
            place: *p,
            usage: *usage,
        })
    }

    /// Merges the usages of overlapping places: whenever one place is a prefix
    /// of another, both usages are replaced by a usage of their longest common
    /// prefix, with the join of their usage types.
    ///
    /// The result satisfies the *disjointness property*: for distinct places
    /// `p`, `p'` in the result, neither is a prefix of the other. Sibling
    /// places (e.g. `x.f` and `x.g`) are already disjoint and are therefore
    /// kept apart, which is what allows a loop that writes `x.f` and reads
    /// `x.g` to require `x.f: E` and `x.g: R` rather than the less precise
    /// `x: E`.
    pub(crate) fn consolidate(&self) -> Self {
        let mut consolidated: HashMap<Place<'tcx>, PlaceUsageType> = HashMap::default();
        for usage in self.iter() {
            let mut place = usage.place;
            let mut usage_type = usage.usage;
            consolidated.retain(|other_place, other_usage| {
                if other_place.is_prefix_of(place) || place.is_prefix_of(*other_place) {
                    place = place.common_prefix(*other_place);
                    usage_type = usage_type.joined(*other_usage);
                    false
                } else {
                    true
                }
            });
            consolidated.insert(place, usage_type);
        }
        PlaceUsages(consolidated)
    }

    /// The usages of this set in the order in which the corresponding places
    /// should be unpacked at a loop head: the places requiring write or
    /// exclusive access first, then the read-only places.
    ///
    /// The order matters: unpacking a place for `Read` first would force a
    /// subsequent exclusive unpack of one of its ancestors to downgrade it.
    pub(crate) fn loop_head_unpack_order(&self) -> Vec<PlaceUsage<'tcx>> {
        let mut usages = self.iter().collect::<Vec<_>>();
        usages.sort_by_key(|usage| {
            (
                usage.usage.is_read(),
                usage.place.local,
                usage.place.projection.len(),
            )
        });
        usages
    }

    /// Convert to a serializable debug representation with string place keys.
    #[cfg(feature = "visualization")]
    pub(crate) fn to_debug_repr<'a, Ctxt: HasCompilerCtxt<'a, 'tcx>>(
        &self,
        ctxt: Ctxt,
    ) -> stmt_graphs::PlaceUsagesDebugRepr
    where
        'tcx: 'a,
    {
        use crate::utils::display::DisplayWithCtxt;
        stmt_graphs::PlaceUsagesDebugRepr::new(
            self.0
                .iter()
                .map(|(p, usage)| (p.to_short_string(ctxt), *usage))
                .collect(),
        )
    }
}

impl<'tcx> FromIterator<PlaceUsage<'tcx>> for PlaceUsages<'tcx> {
    fn from_iter<T: IntoIterator<Item = PlaceUsage<'tcx>>>(iter: T) -> Self {
        PlaceUsages(
            iter.into_iter()
                .map(|u| (u.place, u.usage))
                .collect::<HashMap<Place, PlaceUsageType>>(),
        )
    }
}

#[derive(Clone)]
pub(crate) struct LoopPlaceUsageAnalysis<'tcx> {
    /// This map contains, for each loop head, the set of places that are used in the loop.
    ///
    /// Note that if the loop does not use any places, there will still be an
    /// entry in this table (the corresponding value will be an empty set).
    /// Accordingly, this data structure also can be used to check whether a
    /// block is a loop head.
    loop_used_places: HashMap<BasicBlock, PlaceUsages<'tcx>>,
}

struct UsageVisitor<'a, 'tcx> {
    used_places: &'a mut LoopPlaceUsageDomain<'tcx>,
}

impl<'a, 'tcx> UsageVisitor<'a, 'tcx> {
    fn new(used_places: &'a mut LoopPlaceUsageDomain<'tcx>) -> Self {
        Self { used_places }
    }
}

impl<'tcx> FallableVisitor<'tcx> for UsageVisitor<'_, 'tcx> {
    fn visit_place_fallable(
        &mut self,
        place: Place<'tcx>,
        context: PlaceContext,
        _location: mir::Location,
    ) {
        match context {
            PlaceContext::MutatingUse(MutatingUseContext::Projection) | PlaceContext::NonUse(_) => {
            }
            PlaceContext::MutatingUse(
                MutatingUseContext::Borrow
                | MutatingUseContext::RawBorrow
                | MutatingUseContext::Drop,
            )
            | PlaceContext::NonMutatingUse(NonMutatingUseContext::Move) => {
                let _ = self.used_places.update(place, PlaceUsageType::Exclusive);
            }
            PlaceContext::MutatingUse(_) => {
                let _ = self.used_places.update(place, PlaceUsageType::Write);
            }
            PlaceContext::NonMutatingUse(_) => {
                let _ = self.used_places.update(place, PlaceUsageType::Read);
            }
        }
    }
}

struct SingleLoopAnalysis<'loops> {
    loop_id: LoopId,
    loop_analysis: &'loops LoopAnalysis,
}

impl<'tcx> Analysis<'tcx> for SingleLoopAnalysis<'_> {
    type Domain = LoopPlaceUsageDomain<'tcx>;
    type Direction = Forward;

    const NAME: &'static str = "SingleLoopAnalysis";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        LoopPlaceUsageDomain {
            used_places: PlaceUsages::default(),
        }
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, _state: &mut Self::Domain) {}

    fn apply_statement_effect(
        &self,
        state: &mut Self::Domain,
        statement: &mir::Statement<'tcx>,
        location: mir::Location,
    ) {
        if self.loop_analysis.in_loop(location.block, self.loop_id) {
            let mut visitor = UsageVisitor::new(state);
            visitor
                .visit_statement_fallable(statement, location)
                .unwrap();
        }
    }

    fn apply_terminator_effect(
        &self,
        state: &mut Self::Domain,
        terminator: &mir::Terminator<'tcx>,
        location: mir::Location,
    ) {
        if self.loop_analysis.in_loop(location.block, self.loop_id) {
            let mut visitor = UsageVisitor::new(state);
            visitor
                .visit_terminator_fallable(terminator, location)
                .unwrap();
        }
    }
}

impl DebugWithContext<AnalysisEngine<SingleLoopAnalysis<'_>>> for LoopPlaceUsageDomain<'_> {}

impl<'tcx> LoopPlaceUsageAnalysis<'tcx> {
    pub(crate) fn is_loop_head(&self, block: BasicBlock) -> bool {
        self.loop_used_places.contains_key(&block)
    }

    pub(crate) fn new(tcx: ty::TyCtxt<'tcx>, body: &Body<'tcx>, analysis: &LoopAnalysis) -> Self {
        let mut loop_used_places: HashMap<BasicBlock, PlaceUsages<'tcx>> = HashMap::default();
        for (loop_id, loop_head) in analysis.loop_heads.iter_enumerated() {
            let analysis = SingleLoopAnalysis {
                loop_id,
                loop_analysis: analysis,
            };
            let results = compute_fixpoint(AnalysisEngine(analysis), tcx, body);
            let mut cursor = results.into_results_cursor(body);
            cursor.seek_to_block_start(*loop_head);
            loop_used_places.insert(*loop_head, cursor.get().used_places.clone());
        }
        Self { loop_used_places }
    }

    /// Returns the set of places that are used in the loop with head `block`.
    ///
    /// Returns `None` if `block` is not a loop head.
    /// If `block` is a loop head, but the loop does not use any places, this
    /// will return an empty set.
    pub(crate) fn get_used_places(&self, block: BasicBlock) -> Option<&PlaceUsages<'tcx>> {
        self.loop_used_places.get(&block)
    }
}
