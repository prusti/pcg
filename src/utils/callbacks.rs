use derive_more::From;

use crate::{
    borrow_checker::{
        InScopeBorrows, RustBorrowCheckerInterface,
        r#impl::{NllBorrowCheckerImpl, PoloniusBorrowChecker},
    },
    borrow_pcg::region_projection::{OverrideRegionDebugString, PcgRegion},
    pcg::{self},
    rustc_interface::{
        borrowck::{
            BorrowIndex, BorrowSet, LocationTable, PoloniusInput, PoloniusOutput,
            RegionInferenceContext,
        },
        middle::{mir::Location, ty::RegionVid},
    },
};

#[cfg(feature = "visualization")]
use crate::visualization::bc_facts_graph::RegionPrettyPrinter;

fn cargo_crate_name() -> Option<String> {
    std::env::var("CARGO_CRATE_NAME").ok()
}

/// Is the current compilation running under cargo? Returns true when compiling
/// a crate, but false when compiling a build script.
pub fn in_cargo_crate() -> bool {
    cargo_crate_name().is_some()
}

/// Is the current compilation running under cargo? Either compiling a crate or
/// a build script.
pub fn in_cargo() -> bool {
    std::env::var("CARGO").ok().is_some()
}

#[derive(From)]
#[allow(clippy::large_enum_variant)]
pub enum RustBorrowCheckerImpl<'mir, 'tcx> {
    Polonius(PoloniusBorrowChecker<'mir, 'tcx>),
    Nll(NllBorrowCheckerImpl<'mir, 'tcx>),
}

impl<'mir, 'tcx: 'mir> OverrideRegionDebugString for RustBorrowCheckerImpl<'mir, 'tcx> {
    fn override_region_debug_string(&self, region: RegionVid) -> Option<&str> {
        match self {
            RustBorrowCheckerImpl::Polonius(bc) => bc.override_region_debug_string(region),
            RustBorrowCheckerImpl::Nll(bc) => bc.override_region_debug_string(region),
        }
    }
}

impl<'tcx> RustBorrowCheckerInterface<'tcx> for RustBorrowCheckerImpl<'_, 'tcx> {
    fn borrows_in_scope_at(&self, location: Location, before: bool) -> InScopeBorrows {
        match self {
            RustBorrowCheckerImpl::Polonius(bc) => bc.borrows_in_scope_at(location, before),
            RustBorrowCheckerImpl::Nll(bc) => bc.borrows_in_scope_at(location, before),
        }
    }

    fn is_live(&self, node: pcg::PcgNode<'tcx>, location: Location) -> bool {
        match self {
            RustBorrowCheckerImpl::Polonius(bc) => bc.is_live(node, location),
            RustBorrowCheckerImpl::Nll(bc) => bc.is_live(node, location),
        }
    }

    fn borrow_set(&self) -> &BorrowSet<'tcx> {
        match self {
            RustBorrowCheckerImpl::Polonius(bc) => bc.borrow_set(),
            RustBorrowCheckerImpl::Nll(bc) => bc.borrow_set(),
        }
    }

    fn borrow_in_scope_at(&self, borrow_index: BorrowIndex, location: Location) -> bool {
        match self {
            RustBorrowCheckerImpl::Polonius(bc) => bc.borrow_in_scope_at(borrow_index, location),
            RustBorrowCheckerImpl::Nll(bc) => bc.borrow_in_scope_at(borrow_index, location),
        }
    }

    fn origin_contains_loan_at(
        &self,
        region: PcgRegion,
        loan: BorrowIndex,
        location: Location,
    ) -> bool {
        match self {
            RustBorrowCheckerImpl::Polonius(bc) => {
                bc.origin_contains_loan_at(region, loan, location)
            }
            RustBorrowCheckerImpl::Nll(bc) => bc.origin_contains_loan_at(region, loan, location),
        }
    }

    fn input_facts(&self) -> &PoloniusInput {
        match self {
            RustBorrowCheckerImpl::Polonius(bc) => bc.input_facts(),
            RustBorrowCheckerImpl::Nll(bc) => bc.input_facts(),
        }
    }

    fn region_infer_ctxt(&self) -> &RegionInferenceContext<'tcx> {
        match self {
            RustBorrowCheckerImpl::Polonius(bc) => bc.region_infer_ctxt(),
            RustBorrowCheckerImpl::Nll(bc) => bc.region_infer_ctxt(),
        }
    }

    fn location_table(&self) -> &LocationTable {
        match self {
            RustBorrowCheckerImpl::Polonius(bc) => bc.location_table(),
            RustBorrowCheckerImpl::Nll(bc) => bc.location_table(),
        }
    }

    fn polonius_output(&self) -> Option<&PoloniusOutput> {
        match self {
            RustBorrowCheckerImpl::Polonius(bc) => bc.polonius_output(),
            RustBorrowCheckerImpl::Nll(bc) => bc.polonius_output(),
        }
    }
}

#[cfg(feature = "visualization")]
impl<'mir, 'tcx> RustBorrowCheckerImpl<'mir, 'tcx> {
    pub fn region_pretty_printer(&mut self) -> &mut RegionPrettyPrinter<'mir, 'tcx> {
        match self {
            RustBorrowCheckerImpl::Polonius(bc) => &mut bc.borrow_checker_data.pretty_printer,
            RustBorrowCheckerImpl::Nll(bc) => &mut bc.borrow_checker_data.pretty_printer,
        }
    }

    pub fn region_infer_ctxt(&self) -> &RegionInferenceContext<'tcx> {
        match self {
            RustBorrowCheckerImpl::Polonius(bc) => bc.borrow_checker_data.region_cx,
            RustBorrowCheckerImpl::Nll(bc) => bc.borrow_checker_data.region_cx,
        }
    }
}
