use crate::{
    borrow_pcg::state::BorrowsState,
    rustc_interface::middle::mir,
};

pub(crate) struct JoinOwnedData<'a, 'pcg, 'tcx, T> {
    pub(crate) owned: T,
    pub(crate) borrows: &'pcg mut BorrowsState<'a, 'tcx>,
    pub(crate) block: mir::BasicBlock,
}

impl<'a, 'pcg, 'tcx, T> JoinOwnedData<'a, 'pcg, 'tcx, T> {
    pub(crate) fn map_owned<'slf: 'res, 'res, U: 'res>(
        &'slf mut self,
        f: impl Fn(&'slf mut T) -> U,
    ) -> JoinOwnedData<'a, 'res, 'tcx, U>
    where
        'pcg: 'res,
    {
        JoinOwnedData {
            owned: f(&mut self.owned),
            borrows: self.borrows,
            block: self.block,
        }
    }
}

impl<'a, 'pcg, 'tcx, T> JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut T> {
    pub(crate) fn reborrow<'slf>(&'slf mut self) -> JoinOwnedData<'a, 'slf, 'tcx, &'slf mut T> {
        JoinOwnedData {
            owned: self.owned,
            borrows: self.borrows,
            block: self.block,
        }
    }
}
