use crate::{
    DebugLines, HasSettings,
    action::{BorrowPcgAction, PcgAction},
    borrow_pcg::action::LabelPlaceReason,
    capability_gte,
    error::PcgError,
    owned_pcg::{
        ExpandedPlace, OwnedPcgNode, RepackExpand, RepackOp,
        join::{data::JoinOwnedData, obtain::JoinObtainer},
    },
    pcg::{
        CapabilityKind, CapabilityLike, PositiveCapability, SymbolicCapability,
        obtain::{ActionApplier, HasSnapshotLocation, PlaceCollapser},
        place_capabilities::PlaceCapabilitiesReader,
    },
    pcg_validity_assert,
    utils::{
        HasBorrowCheckerCtxt, Place, data_structures::HashSet, display::DisplayWithCompilerCtxt,
    },
};

enum JoinDifferentExpansionsResult<'tcx> {
    ExpandedForRead(RepackExpand<'tcx>),
    ExpandedForNoCapability,
    Collapsed(Vec<RepackOp<'tcx>>),
}

impl<'tcx> JoinDifferentExpansionsResult<'tcx> {
    fn actions(self) -> Vec<RepackOp<'tcx>> {
        match self {
            JoinDifferentExpansionsResult::ExpandedForRead(action) => {
                vec![RepackOp::Expand(action)]
            }
            JoinDifferentExpansionsResult::ExpandedForNoCapability => vec![],
            JoinDifferentExpansionsResult::Collapsed(actions) => actions,
        }
    }
}

enum JoinExpandedPlaceResult<'tcx> {
    JoinedWithSameExpansion(Vec<RepackOp<'tcx>>),
    CreatedExpansion(Vec<RepackOp<'tcx>>),
    JoinedWithOtherExpansions(JoinDifferentExpansionsResult<'tcx>),
    CollapsedOtherExpansion,
}

impl<'tcx> JoinExpandedPlaceResult<'tcx> {
    fn actions(self) -> Vec<RepackOp<'tcx>> {
        match self {
            JoinExpandedPlaceResult::JoinedWithSameExpansion(actions)
            | JoinExpandedPlaceResult::CreatedExpansion(actions) => actions,
            JoinExpandedPlaceResult::JoinedWithOtherExpansions(result) => result.actions(),
            JoinExpandedPlaceResult::CollapsedOtherExpansion => vec![],
        }
    }

    fn performed_collapse(&self) -> bool {
        matches!(
            self,
            JoinExpandedPlaceResult::JoinedWithOtherExpansions(
                JoinDifferentExpansionsResult::Collapsed(_)
            ) | JoinExpandedPlaceResult::CollapsedOtherExpansion
        )
    }
}

impl<'pcg, 'a: 'pcg, 'tcx> JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut OwnedPcgNode<'tcx>> {
    fn join_different_expansions_from_place<'other>(
        &mut self,
        other: &mut JoinOwnedData<'a, 'pcg, 'tcx, &'other mut OwnedPcgNode<'tcx>>,
        other_expansion: &ExpandedPlace<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<JoinDifferentExpansionsResult<'tcx>, PcgError<'tcx>>
    where
        'pcg: 'other,
        'tcx: 'a,
    {
        todo!()
    }

    fn expand_from_place_with_caps(
        &mut self,
        other: &mut JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut OwnedPcgNode<'tcx>>,
        expansion: &ExpandedPlace<'tcx>,
        self_cap: SymbolicCapability,
        other_cap: SymbolicCapability,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError<'tcx>>
    where
        'tcx: 'a,
    {
        todo!()
    }

    fn join_all_places_in_expansion(
        &mut self,
        other: &JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut OwnedPcgNode<'tcx>>,
        expansion: &ExpandedPlace<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError<'tcx>>
    where
        'tcx: 'a,
    {
        let mut actions = vec![];
        for expansion_place in expansion.expansion_places(ctxt).unwrap() {
            actions.extend(self.join_owned_places(other, expansion_place, ctxt)?);
        }
        Ok(actions)
    }

    /// See <https://prusti.github.io/pcg-docs/join.html#local-expansions-join--joine>
    fn join_other_expanded_place(
        &mut self,
        other: &mut JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut OwnedPcgNode<'tcx>>,
        other_expansion: &ExpandedPlace<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<JoinExpandedPlaceResult<'tcx>, PcgError<'tcx>>
    where
        'tcx: 'a,
    {
        todo!()
    }

    fn visit_each_other_expansion_iteration(
        &mut self,
        other: &mut JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut OwnedPcgNode<'tcx>>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError<'tcx>>
    where
        'tcx: 'a,
    {
        todo!()
    }

    fn visit_each_other_expansion(
        &mut self,
        mut other: JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut OwnedPcgNode<'tcx>>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError<'tcx>>
    where
        'tcx: 'a,
    {
        let mut actions = vec![];
        let mut iteration = 0;
        loop {
            iteration += 1;
            tracing::debug!("Iteration {}", iteration);
            let iteration_actions = self.visit_each_other_expansion_iteration(&mut other, ctxt)?;
            if iteration_actions.is_empty() {
                break;
            }
            actions.extend(iteration_actions);
        }
        Ok(actions)
    }

    fn render_debug_graph<'slf>(
        &'slf self,
        comment: &str,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>,
    ) where
        'tcx: 'slf,
        'tcx: 'a,
    {
    }

    fn join_leaf_read_and_write_capabilities(
        &mut self,
        other: &JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut OwnedPcgNode<'tcx>>,
        place: Place<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError<'tcx>>
    where
        'tcx: 'a,
    {
        todo!()
    }

    pub(crate) fn join_owned_places(
        &mut self,
        other: &JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut OwnedPcgNode<'tcx>>,
        place: Place<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError<'tcx>>
    where
        'tcx: 'a,
    {
        todo!()
    }

    pub(crate) fn join(
        mut self,
        mut other: JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut OwnedPcgNode<'tcx>>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError<'tcx>>
    where
        'tcx: 'a,
    {
        todo!()
    }
}
