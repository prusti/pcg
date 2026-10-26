use crate::{
    action::PcgAction,
    borrow_pcg::state::{BorrowStateMutRef, BorrowsStateLike},
    error::PcgError,
    owned_pcg::{LocalExpansions, RepackOp, join::data::JoinOwnedData},
    pcg::{
        CompilerCtxtWithSettings,
        obtain::{ActionApplier, HasSnapshotLocation, PlaceCollapser},
        place_capabilities::PlaceCapabilities,
    },
    rustc_interface::middle::mir,
    utils::{CompilerCtxt, Place, SnapshotLocation, data_structures::HashSet},
};

pub(crate) type JoinCtxt<'a, 'tcx> = CompilerCtxtWithSettings<'a, 'tcx>;

pub(crate) struct JoinObtainer<'pcg: 'exp, 'exp, 'slf, 'a, 'tcx> {
    pub(crate) ctxt: JoinCtxt<'a, 'tcx>,
    pub(crate) data: &'slf mut JoinOwnedData<'a, 'pcg, 'tcx, &'exp mut LocalExpansions<'tcx>>,
    pub(crate) actions: Vec<PcgAction<'tcx>>,
}

impl HasSnapshotLocation for JoinObtainer<'_, '_, '_, '_, '_> {
    fn prev_snapshot_location(&self) -> SnapshotLocation {
        self.data.snapshot_location
    }
}

impl<'tcx> ActionApplier<'tcx> for JoinObtainer<'_, '_, '_, '_, 'tcx> {
    fn apply_action(&mut self, action: PcgAction<'tcx>) -> Result<(), PcgError> {
        match action {
            PcgAction::Borrow(mut action) => {
                self.data
                    .borrows
                    .apply_action(&mut action, self.data.capabilities, self.ctxt);
                self.actions.push(action.into());
            }
            PcgAction::Owned(action) => match action.kind {
                RepackOp::Collapse(collapse) => {
                    let changes = self.data.owned.perform_collapse_action(
                        collapse,
                        self.data.capabilities,
                        self.ctxt,
                    );
                    self.actions.push(action.with_capabilities(changes).into());
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

    fn capabilities(&mut self) -> &mut PlaceCapabilities<'tcx> {
        self.data.capabilities
    }

    /// Owned leaf places that are not borrowed.
    fn leaf_places(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> HashSet<Place<'tcx>> {
        let owned_places = self.blocked_owned_places(ctxt);
        self.data
            .owned
            .leaf_places(ctxt)
            .into_iter()
            .map(Into::into)
            .filter(|p| !owned_places.contains(p))
            .collect()
    }

    fn blocked_owned_places(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> HashSet<Place<'tcx>> {
        self.data.borrows.graph().owned_places(ctxt)
    }
}
