//! Defines the interface for exposing borrow-checker information to the PCG.
//!
//! Also includes implementations for the Polonius and NLL borrow-checkers.

use std::{collections::BTreeSet, iter::zip, ops::ControlFlow};

extern crate rustc_middle;
use rustc_middle::ty;

use crate::{
    borrow_checker::r#impl::get_reserve_location,
    borrow_pcg::{
        GeneralizedLifetime,
        region_projection::PcgRegion,
        visitor::{OpaqueTy, erase_regions},
    },
    pcg::PcgNode,
    rustc_interface::{
        borrowck::{
            BorrowData, BorrowIndex, BorrowSet, LocationTable, PlaceConflictBias, PoloniusInput,
            PoloniusOutput, RegionInferenceContext, places_conflict,
        },
        data_structures::fx::FxIndexSet,
        index,
        middle::{
            mir::{self, Location},
            ty::RegionVid,
        },
    },
    utils::{
        CompilerCtxt, Place,
        display::{
            DisplayCtxtFor, DisplayOutput, DisplayWithCompilerCtxt, DisplayWithCtxt, OutputMode,
        },
    },
};

pub mod r#impl;

pub(crate) trait BorrowLike<'tcx> {
    fn get_borrowed_place(&self) -> Place<'tcx>;
}

impl<'tcx> BorrowLike<'tcx> for BorrowData<'tcx> {
    fn get_borrowed_place(&self) -> Place<'tcx> {
        self.borrowed_place().into()
    }
}

trait HasPcgRegion<'tcx> {
    fn pcg_region(&self) -> PcgRegion<'tcx>;
}

impl<'tcx> HasPcgRegion<'tcx> for BorrowData<'tcx> {
    fn pcg_region(&self) -> PcgRegion<'tcx> {
        self.region().into()
    }
}

impl<'tcx, T: RustBorrowCheckerInterface<'tcx> + DisplayCtxtFor<RegionVid>>
    BorrowCheckerInterface<'tcx> for T
{
    fn tcx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx()
    }

    fn fr_fn_body(&self) -> RegionVid {
        RustBorrowCheckerInterface::fr_fn_body(self)
    }

    fn is_dead(&self, node: PcgNode<'tcx>, location: Location) -> bool {
        !self.is_live(node, location)
    }

    fn twophase_borrow_activations(&self, location: Location) -> BTreeSet<Location> {
        #[rustversion::since(2026-07-28)]
        let borrow_idxs: &[BorrowIndex] = self.borrow_set().activations_at_location(&location);
        #[rustversion::before(2026-07-28)]
        let borrow_idxs: &[BorrowIndex] = self
            .borrow_set()
            .activation_map()
            .get(&location)
            .map_or(&[], |idxs| &idxs[..]);
        borrow_idxs
            .iter()
            .map(|idx| get_reserve_location(&self.borrow_set()[*idx]))
            .collect()
    }

    fn borrows_blocking(
        &self,
        blocked_place: Place<'tcx>,
        location: Location,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Vec<BorrowData<'tcx>> {
        let mut borrows = vec![];
        each_borrow_involving_path(
            &mut (),
            ctxt,
            blocked_place,
            self.borrow_set(),
            |borrow_index| self.borrow_in_scope_at(borrow_index, location),
            |_this, _, borrow| {
                borrows.push(borrow.clone());
                ControlFlow::Continue(())
            },
        );
        borrows
    }

    fn region_to_borrow_index(&self, region: PcgRegion<'tcx>) -> Option<BorrowIndex> {
        RustBorrowCheckerInterface::region_to_borrow_index(self, region)
    }

    fn is_directly_blocked(
        &self,
        blocked_place: Place<'tcx>,
        location: Location,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut conflict = false;
        each_borrow_involving_path(
            &mut (),
            ctxt,
            blocked_place,
            self.borrow_set(),
            |borrow_index| self.borrow_in_scope_at(borrow_index, location),
            |_this, _borrow_index, borrow| {
                if borrow.get_borrowed_place() == blocked_place {
                    conflict = true;
                    ControlFlow::Break(())
                } else {
                    ControlFlow::Continue(())
                }
            },
        );
        conflict
    }

    fn blocks(
        &self,
        blocking_place: Place<'tcx>,
        blocked_place: Place<'tcx>,
        location: Location,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut conflict = false;
        each_borrow_involving_path(
            &mut (),
            ctxt,
            blocked_place,
            self.borrow_set(),
            |borrow_index| self.borrow_in_scope_at(borrow_index, location),
            |_this, borrow_index, _borrow| {
                tracing::debug!(
                    "Checking if {} contains {:?} at {:?}",
                    blocking_place.display_string(ctxt),
                    borrow_index,
                    location
                );
                if blocking_place
                    .regions(ctxt)
                    .iter()
                    .any(|region| self.origin_contains_loan_at(*region, borrow_index, location))
                {
                    conflict = true;
                    ControlFlow::Break(())
                } else {
                    ControlFlow::Continue(())
                }
            },
        );
        conflict
    }

    fn as_dyn(&self) -> &dyn BorrowCheckerInterface<'tcx> {
        self
    }

    fn outlives(&self, sup: PcgRegion<'tcx>, sub: PcgRegion<'tcx>, _location: Location) -> bool {
        self.outlives_everywhere(sup, sub)
    }

    fn polonius_output(&self) -> Option<&PoloniusOutput> {
        self.polonius_output()
    }

    fn input_facts(&self) -> &PoloniusInput {
        self.input_facts()
    }

    fn rust_borrow_checker(&self) -> Option<&dyn RustBorrowCheckerInterface<'tcx>> {
        Some(self)
    }
}

pub trait BorrowCheckerInterface<'tcx>: DisplayCtxtFor<RegionVid> {
    /* Main Interface Start */

    fn tcx(&self) -> ty::TyCtxt<'tcx>;

    /// The universal region for the function body, which all universal
    /// regions outlive.
    fn fr_fn_body(&self) -> RegionVid;

    /// Answers the question: Does `node` contain borrow extents that are not
    /// in scope at `location`?
    fn is_dead(&self, node: PcgNode<'tcx>, location: Location) -> bool;

    fn is_directly_blocked(
        &self,
        blocked_place: Place<'tcx>,
        location: Location,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool;

    fn blocks(
        &self,
        blocking_place: Place<'tcx>,
        blocked_place: Place<'tcx>,
        location: Location,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool;

    /// Returns true iff `sup` is required to outlive `sub` at `location`.
    fn outlives(&self, sup: PcgRegion<'tcx>, sub: PcgRegion<'tcx>, location: Location) -> bool;

    /// Like [`Self::outlives`], but for generalized lifetimes.
    ///
    /// Must return `true` whenever borrows under `sup` may flow into `sub`.
    fn outlives_generalized(
        &self,
        sup: GeneralizedLifetime<'tcx>,
        sub: GeneralizedLifetime<'tcx>,
        location: Location,
    ) -> bool {
        match (sup, sub) {
            (GeneralizedLifetime::Region(sup), GeneralizedLifetime::Region(sub)) => {
                self.outlives(sup, sub, location)
            }
            // `'static` is the only region that outlives every region an opaque type may contain.
            (GeneralizedLifetime::Region(sup), GeneralizedLifetime::RegionsIn(_)) => {
                self.outlives(sup, PcgRegion::ReStatic, location)
            }
            (
                GeneralizedLifetime::RegionsIn(sup_opaque),
                GeneralizedLifetime::RegionsIn(sub_opaque),
            ) => match (sup_opaque, sub_opaque) {
                // We consider two alias types to outlive each other if they are the same after erasing regions,
                // and all regions are equal. For example, we consider <T as Tr<'?7>>::Assoc to outlive 
                // <T as Tr<'?8>>::Assoc if '?7: '?8 and '?8: '?7.
                (OpaqueTy::Alias(sup_ty), OpaqueTy::Alias(sub_ty)) => {
                    let tcx = self.tcx();
                    if erase_regions(sup_ty, tcx) != erase_regions(sub_ty, tcx) {
                        return false;
                    }
                    // Keeps duplicates, so that the regions can be paired by position.
                    let free_regions_in_order = |ty: ty::Ty<'tcx>| -> Vec<PcgRegion<'tcx>> {
                        let mut regions = vec![];
                        tcx.for_each_free_region(&ty, |r| regions.push(r.into()));
                        regions
                    };
                    let sup_regions = free_regions_in_order(sup_ty);
                    let sub_regions = free_regions_in_order(sub_ty);
                    if sup_regions.len() != sub_regions.len() {
                        return false;
                    }
                    zip(sup_regions, sub_regions).all(|(sup_region, sub_region)| {
                        self.outlives(sup_region.into(), sub_region.into(), location)
                        && self.outlives(sub_region.into(), sup_region.into(), location)
                    })
                }
                (_, _) => sup_opaque == sub_opaque,
            },
            // The regions in `T` are chosen by the caller and outlive the function
            // body. An alias may also contain the regions in its arguments.
            (GeneralizedLifetime::RegionsIn(opaque), GeneralizedLifetime::Region(sub)) => {
                let alias_regions_outlive_sub = match opaque {
                    OpaqueTy::Param(_) => true,
                    OpaqueTy::Alias(ty) => self
                        .tcx()
                        .all_free_regions_meet(&ty, |r| self.outlives(r.into(), sub, location)),
                };
                alias_regions_outlive_sub
                    && self.outlives(PcgRegion::RegionVid(self.fr_fn_body()), sub, location)
            }
        }
    }

    fn borrows_blocking(
        &self,
        blocked_place: Place<'tcx>,
        location: Location,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Vec<BorrowData<'tcx>>;

    /// Returns the set of two-phase borrows that activate at `location`.
    /// Each borrow in the returned set is represented by the MIR location
    /// that it was created at.
    fn twophase_borrow_activations(&self, location: Location) -> BTreeSet<Location>;

    /* Main Interface End */

    /// Returns true iff `reg1` outlives `reg2` and `reg2` outlives `reg1`.
    fn same_region(
        &self,
        reg1: PcgRegion<'tcx>,
        reg2: PcgRegion<'tcx>,
        location: Location,
    ) -> bool {
        self.outlives(reg1, reg2, location) && self.outlives(reg2, reg1, location)
    }

    /// Like [`Self::same_region`], but for generalized lifetimes.
    fn same_region_generalized(
        &self,
        reg1: GeneralizedLifetime<'tcx>,
        reg2: GeneralizedLifetime<'tcx>,
        location: Location,
    ) -> bool {
        self.outlives_generalized(reg1, reg2, location)
            && self.outlives_generalized(reg2, reg1, location)
    }

    // Implementors of this trait should be dyn-safe
    fn as_dyn(&self) -> &dyn BorrowCheckerInterface<'tcx>;

    /*
     * The remaining methods are only used for debugging / visualization.
     */

    /// If this is a Rust borrow checker, return its interface.
    /// TODO: Get rid of this at some point
    fn rust_borrow_checker(&self) -> Option<&dyn RustBorrowCheckerInterface<'tcx>>;

    // DEBUG ONLY
    /// If the borrow checker is based on Polonius, it can define this method to
    /// expose its output facts. This is only used for debugging /
    /// visualization.
    /// TODO: Remove
    fn polonius_output(&self) -> Option<&PoloniusOutput>;

    /// Currently only used for associating borrows with their indexes for
    /// visualization purposes.
    /// TODO: Remove
    fn region_to_borrow_index(&self, region: PcgRegion<'tcx>) -> Option<BorrowIndex>;

    // TODO: Remove, only for visualization
    fn input_facts(&self) -> &PoloniusInput;

    /// Returns an iterator over all `RegionVid`s for this body.
    ///
    /// The implementation is a hack: it extracts region vids from the
    /// constraint SCC indices in the region inference context. This is
    /// currently used in
    /// [`DefinedFnCallWithCallTys::normalize_sig`](crate::borrow_pcg::edge::abstraction::function::DefinedFnCallWithCallTys)
    /// to pre-populate an inference context with the correct number of region
    /// variables before performing type normalization. This method should be
    /// removed if we find a better way to perform that normalization.
    fn iter_region_vids<'slf>(&'slf self) -> Box<dyn Iterator<Item = RegionVid> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(
            self.rust_borrow_checker()
                .unwrap()
                .region_infer_ctxt()
                .constraint_sccs()
                .scc_indices()
                .iter_enumerated()
                .map(move |(region_vid, _)| region_vid),
        )
    }
}

impl<'a, 'tcx> DisplayWithCtxt<&'a dyn BorrowCheckerInterface<'tcx>> for RegionVid {
    fn display_output(
        &self,
        ctxt: &'a dyn BorrowCheckerInterface<'tcx>,
        mode: OutputMode,
    ) -> DisplayOutput {
        ctxt.display_value(self, mode)
    }
}

#[rustversion::before(2025-03-02)]
pub type InScopeBorrows = index::bit_set::BitSet<BorrowIndex>;

#[rustversion::since(2025-03-02)]
pub type InScopeBorrows = index::bit_set::MixedBitSet<BorrowIndex>;

/// An interface to the results of the borrow-checker analysis. The PCG queries
/// this interface as part of its analysis, for example, to identify when borrows
/// expire.
pub trait RustBorrowCheckerInterface<'tcx> {
    fn tcx(&self) -> ty::TyCtxt<'tcx>;

    /// The universal region for `'static`.
    fn fr_static(&self) -> RegionVid;

    /// The universal region for the function body, which all universal
    /// regions outlive.
    fn fr_fn_body(&self) -> RegionVid;

    /// Returns true iff the node is live *before* `location`. A node is live
    /// iff:
    /// - it is a place node, and the place is live
    /// - it is a lifetime projection node, and the lifetime is live
    ///
    /// For lifetimes, we use the notion of liveness defined here in
    /// <https://rust-lang.github.io/rfcs/2094-nll.html#liveness>:
    ///
    /// > A lifetime `L` is live at a point `P` if there is some variable `p` which is
    /// > live at `P`, and `L` appears in the type of `p`
    ///
    /// However, as referenced in the above link, there are some subtleties
    /// related to places that will be dropped. Follow the link for more details.
    ///
    /// Note that the return place and its lifetime projections will always be
    /// live.
    fn is_live(&self, node: PcgNode<'tcx>, location: Location) -> bool;

    fn borrow_set(&self) -> &BorrowSet<'tcx>;

    /// Returns the set of borrows that are live either before or after
    /// `location`.
    fn borrows_in_scope_at(&self, location: Location, before: bool) -> InScopeBorrows;

    fn borrow_in_scope_at(&self, borrow_index: BorrowIndex, location: Location) -> bool {
        self.borrows_in_scope_at(location, true)
            .contains(borrow_index)
    }

    fn origin_contains_loan_at(
        &self,
        region: PcgRegion<'tcx>,
        loan: BorrowIndex,
        location: Location,
    ) -> bool;

    fn region_to_borrow_index(&self, region: PcgRegion<'tcx>) -> Option<BorrowIndex> {
        #[rustversion::since(2026-07-28)]
        {
            self.borrow_set()
                .iter_enumerated()
                .find_map(|(index, data)| (data.pcg_region() == region).then_some(index))
        }
        #[rustversion::before(2026-07-28)]
        {
            self.borrow_set()
                .location_map()
                .iter()
                .enumerate()
                .find_map(move |(index, (_, data))| {
                    (data.pcg_region() == region).then_some(index.into())
                })
        }
    }

    fn borrow_index_to_region(&self, borrow_index: BorrowIndex) -> RegionVid {
        self.borrow_set()[borrow_index].region()
    }

    /// If the borrow checker is based on Polonius, it can define this method to
    /// expose its output facts. This is only used for debugging /
    /// visualization.
    fn polonius_output(&self) -> Option<&PoloniusOutput>;

    fn borrows_blocking(
        &self,
        blocked_place: Place<'tcx>,
        location: Location,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Vec<BorrowData<'tcx>> {
        let mut borrows = vec![];
        each_borrow_involving_path(
            &mut (),
            ctxt,
            blocked_place,
            self.borrow_set(),
            |borrow_index| self.borrow_in_scope_at(borrow_index, location),
            |_this, _, borrow| {
                borrows.push(borrow.clone());
                ControlFlow::Continue(())
            },
        );
        borrows
    }

    fn loans_killed_at(&self, location: Location) -> BTreeSet<RegionVid> {
        let location_indices = [
            self.location_table().start_index(location),
            self.location_table().mid_index(location),
        ];
        self.input_facts()
            .loan_killed_at
            .iter()
            .filter(|(_, point)| location_indices.contains(point))
            .map(|(loan, _)| self.borrow_index_to_region(*loan))
            .collect()
    }

    fn input_facts(&self) -> &PoloniusInput;

    fn region_infer_ctxt(&self) -> &RegionInferenceContext<'tcx>;

    fn location_table(&self) -> &LocationTable;

    /// Returns true iff `sup` is required to outlive `sub` everywhere.
    /// This can be useful e.g. for determining outlives relations of
    /// arguments to a function based on its signature.
    fn outlives_everywhere(&self, sup: PcgRegion<'tcx>, sub: PcgRegion<'tcx>) -> bool {
        match (sup, sub) {
            (PcgRegion::RegionVid(sup), PcgRegion::RegionVid(sub)) => {
                self.region_infer_ctxt().eval_outlives(sup, sub)
            }
            (PcgRegion::RegionVid(sup), PcgRegion::ReStatic) => self
                .region_infer_ctxt()
                .eval_outlives(sup, self.fr_static()),
            (PcgRegion::ReStatic, _) => true,
            _ => false,
        }
    }
}

trait BorrowSetLike<'tcx> {
    fn get_borrows_for_local(&self, local: mir::Local) -> Option<&FxIndexSet<BorrowIndex>>;
}

impl<'tcx> BorrowSetLike<'tcx> for BorrowSet<'tcx> {
    fn get_borrows_for_local(&self, local: mir::Local) -> Option<&FxIndexSet<BorrowIndex>> {
        #[rustversion::since(2026-07-28)]
        {
            self.borrows_on_local(local)
        }
        #[rustversion::before(2026-07-28)]
        {
            self.local_map().get(&local)
        }
    }
}

pub(super) fn each_borrow_involving_path<'tcx, F, I, S>(
    s: &mut S,
    ctxt: CompilerCtxt<'_, 'tcx>,
    borrowed_place: Place<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    is_candidate: I,
    mut op: F,
) where
    F: FnMut(&mut S, BorrowIndex, &BorrowData<'tcx>) -> ControlFlow<()>,
    I: Fn(BorrowIndex) -> bool,
{
    // The number of candidates can be large, but borrows for different locals cannot conflict with
    // each other, so we restrict the working set a priori.
    let Some(borrows_for_place_base) = borrow_set.get_borrows_for_local(borrowed_place.local)
    else {
        return;
    };

    // check for loan restricting path P being used. Accounts for
    // borrows of P, P.a.b, etc.
    for &i in borrows_for_place_base {
        if !is_candidate(i) {
            continue;
        }
        let borrowed = &borrow_set[i];

        if places_conflict(
            ctxt.tcx(),
            ctxt.body(),
            borrowed.get_borrowed_place().to_rust_place(ctxt),
            borrowed_place.to_rust_place(ctxt),
            PlaceConflictBias::Overlap,
        ) {
            let ctrl = op(s, i, borrowed);
            if matches!(ctrl, ControlFlow::Break(())) {
                return;
            }
        }
    }
}
