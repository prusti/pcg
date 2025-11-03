#![feature(rustc_private)]

extern crate rustc_hir;
extern crate rustc_middle;

use std::cell::{Cell, RefCell};

use pcg::{
    pcg::BodyWithBorrowckFacts,
    rustc_interface::{
        borrowck,
        data_structures::fx::FxHashMap,
        hir::def_id::LocalDefId,
        middle::{
            query::queries::mir_borrowck::ProvidedValue as MirBorrowck, ty::TyCtxt, util::Providers,
        },
        session::Session,
    },
};

thread_local! {
    static ALLOW_BORROWCK_ERRORS: Cell<bool> = Cell::new(false);
    static BODIES:
        RefCell<FxHashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
        RefCell::new(FxHashMap::default());
}

pub fn allow_borrowck_errors() {
    ALLOW_BORROWCK_ERRORS.set(true);
}

/// # Safety
/// The originally saved body must come from the same `tcx`
pub unsafe fn take_stored_body(tcx: TyCtxt<'_>, def_id: LocalDefId) -> BodyWithBorrowckFacts<'_> {
    BODIES.with(|state| {
        let mut map = state.borrow_mut();
        unsafe {
            std::mem::transmute(map.remove(&def_id).unwrap_or_else(|| {
                panic!("No body found for {}", tcx.def_path_str(def_id.to_def_id()))
            }))
        }
    })
}

pub fn set_mir_borrowck(_session: &Session, providers: &mut Providers) {
    providers.mir_borrowck = mir_borrowck;
}

#[rustversion::before(2025-07-01)]
fn mir_borrowck(tcx: TyCtxt<'_>, def_id: LocalDefId) -> MirBorrowck<'_> {
    let consumer_opts = borrowck::ConsumerOptions::PoloniusInputFacts;
    tracing::debug!(
        "Start mir_borrowck for {}",
        tcx.def_path_str(def_id.to_def_id())
    );
    let body_with_facts = borrowck::get_body_with_borrowck_facts(tcx, def_id, consumer_opts);
    tracing::debug!(
        "End mir_borrowck for {}",
        tcx.def_path_str(def_id.to_def_id())
    );
    save_body(tcx, def_id, body_with_facts.into());
    original_mir_borrowck(tcx, def_id)
}

fn original_mir_borrowck(tcx: TyCtxt<'_>, def_id: LocalDefId) -> MirBorrowck<'_> {
    let mut providers = Providers::default();
    borrowck::provide(&mut providers);
    let original_mir_borrowck = providers.mir_borrowck;
    original_mir_borrowck(tcx, def_id)
}

#[rustversion::since(2025-07-01)]
fn mir_borrowck<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> MirBorrowck<'tcx> {
    let consumer_opts = borrowck::ConsumerOptions::PoloniusInputFacts;
    tracing::debug!(
        "Start mir_borrowck for {}",
        tcx.def_path_str(def_id.to_def_id())
    );
    let body_with_facts = borrowck::get_bodies_with_borrowck_facts(tcx, def_id, consumer_opts);
    tracing::debug!(
        "End mir_borrowck for {}",
        tcx.def_path_str(def_id.to_def_id())
    );
    for (def_id, body) in body_with_facts {
        tracing::debug!("Saving body for {}", tcx.def_path_str(def_id.to_def_id()));
        save_body(tcx, def_id, body.into());
    }
    let result = original_mir_borrowck(tcx, def_id);
    if ALLOW_BORROWCK_ERRORS.get() {
        tcx.dcx().reset_err_count();
    }
    result
}

fn save_body(tcx: TyCtxt<'_>, def_id: LocalDefId, body: BodyWithBorrowckFacts<'_>) {
    unsafe {
        let body: BodyWithBorrowckFacts<'static> = std::mem::transmute(body);
        BODIES.with(|state| {
            let mut map = state.borrow_mut();
            tracing::debug!(
                "Inserting body for {}",
                tcx.def_path_str(def_id.to_def_id())
            );
            assert!(map.insert(def_id, body).is_none());
        });
    }
}
