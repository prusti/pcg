use crate::{
    action::PcgAction,
    borrow_pcg::state::{BorrowStateMutRef, BorrowsStateLike},
    error::PcgError,
    owned_pcg::{LocalExpansions, RepackOp, join::data::JoinOwnedData},
    pcg::{
        obtain::{ActionApplier, HasSnapshotLocation, PlaceCollapser},
        place_capabilities::SymbolicPlaceCapabilities,
    },
    rustc_interface::middle::mir,
    utils::{CompilerCtxt, Place, SnapshotLocation, data_structures::HashSet},
};

pub(crate) struct JoinObtainer<'pcg: 'exp, 'exp, 'slf, 'a, 'tcx> {
    pub(crate) ctxt: CompilerCtxt<'a, 'tcx>,
    pub(crate) data: &'slf mut JoinOwnedData<'a, 'pcg, 'tcx, &'exp mut LocalExpansions<'tcx>>,
    pub(crate) actions: Vec<RepackOp<'tcx>>,
}

impl HasSnapshotLocation for JoinObtainer<'_, '_, '_, '_, '_> {
    fn prev_snapshot_location(&self) -> SnapshotLocation {
        SnapshotLocation::BeforeJoin(self.data.block)
    }
}

impl<'tcx> ActionApplier<'tcx> for JoinObtainer<'_, '_, '_, '_, 'tcx> {
    fn apply_action(&mut self, action: PcgAction<'tcx>) -> Result<(), PcgError> {
        match action {
            PcgAction::Borrow(action) => {
                self.data.borrows.apply_action(
                    action.clone(),
                    self.data.capabilities,
                    self.ctxt,
                )?;
            }
            PcgAction::Owned(action) => match action.kind {
                RepackOp::Collapse(collapse) => {
                    self.data.owned.perform_collapse_action(
                        collapse,
                        self.data.capabilities,
                        self.ctxt,
                    )?;
                    self.actions.push(action.kind);
                }
                RepackOp::RegainLoanedCapability(regained_capability) => {
                    self.data.capabilities.regain_loaned_capability(
                        regained_capability.place,
                        regained_capability.capability.into(),
                        self.data.borrows.as_mut_ref(),
                        self.ctxt,
                    )?;
                    self.actions.push(action.kind);
                }
                _ => unreachable!(),
            },
        }
        Ok(())
    }
}

impl<'a, 'tcx> PlaceCollapser<'a, 'tcx> for JoinObtainer<'_, '_, '_, 'a, 'tcx> {
    fn get_local_expansions(&self, _local: mir::Local) -> &LocalExpansions<'tcx> {
        self.data.owned
    }

    fn borrows_state(&mut self) -> BorrowStateMutRef<'_, 'tcx> {
        self.data.borrows.into()
    }

    fn capabilities(&mut self) -> &mut SymbolicPlaceCapabilities<'tcx> {
        self.data.capabilities
    }

    /// Owned leaf places that are not borrowed.
    fn leaf_places(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> HashSet<Place<'tcx>> {
        let mut leaf_places = self.data.owned.leaf_places(ctxt);
        leaf_places.retain(|p| !self.data.borrows.graph().owned_places(ctxt).contains(p));
        leaf_places
    }
}
