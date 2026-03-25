#![feature(rustc_private)]

extern crate rustc_hir;

use pcg::{
    borrow_pcg::{ArgIdxOrResult, FunctionShape},
    rustc_interface::middle::{mir, ty},
    utils::CompilerCtxt,
};
use pcg_tests::run_pcg_on_str;

/// Extracts the `(DefId, GenericArgsRef)` for the first call to a function
/// whose name contains `target_name` in the given MIR body.
fn find_call<'tcx>(
    body: &mir::Body<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    target_name: &str,
) -> (rustc_hir::def_id::DefId, ty::GenericArgsRef<'tcx>) {
    body.basic_blocks
        .iter()
        .find_map(|bb| {
            let term = bb.terminator();
            if let mir::TerminatorKind::Call { ref func, .. } = term.kind {
                let func_ty = func.ty(body, tcx);
                if let ty::TyKind::FnDef(def_id, substs) = func_ty.kind() {
                    if tcx.def_path_str(*def_id).contains(target_name) {
                        return Some((*def_id, *substs));
                    }
                }
            }
            None
        })
        .unwrap_or_else(|| panic!("should find a call to {target_name}"))
}

/// Builds both the sig shape (identity substs) and the sig-derived call shape
/// (caller substs) for a callee found in the current body, and asserts they
/// are equal.
fn sig_and_call_shapes<'a, 'tcx: 'a>(
    ctxt: CompilerCtxt<'a, 'tcx>,
    callee_name: &str,
) -> (FunctionShape, FunctionShape) {
    let body = ctxt.body();
    let (def_id, caller_substs) = find_call(body, ctxt.tcx(), callee_name);
    let identity_substs = ty::GenericArgs::identity_for_item(ctxt.tcx(), def_id);

    let sig_shape = FunctionShape::for_fn(def_id, identity_substs, ctxt).unwrap();
    let call_shape = FunctionShape::for_fn(def_id, caller_substs, ctxt).unwrap();

    assert_eq!(
        sig_shape, call_shape,
        "sig-derived call shape should equal the sig shape"
    );

    (sig_shape, call_shape)
}

fn assert_choose_shape(shape: &FunctionShape) {
    let (inputs, outputs) = shape.clone().take_inputs_and_outputs();
    assert_eq!(inputs.len(), 2, "choose has 2 inputs (one region per arg)");
    assert_eq!(outputs.len(), 1, "choose has 1 output (result region)");

    let edges: Vec<_> = shape.edges().collect();
    assert_eq!(edges.len(), 2, "choose has 2 edges: arg0->result, arg1->result");

    let mut edge_input_bases: Vec<usize> = edges
        .iter()
        .map(|e| *e.input().base())
        .collect();
    edge_input_bases.sort();
    assert_eq!(edge_input_bases, vec![0, 1], "edges come from arg0 and arg1");

    for edge in &edges {
        assert_eq!(
            edge.output().base(),
            ArgIdxOrResult::Result,
            "all edges target the result"
        );
    }
}

/// Without an outlives constraint between `'a` and `'b`, only arg0 connects
/// to the result (since `'b` does not outlive `'a`).
fn assert_choose_no_outlives_shape(shape: &FunctionShape) {
    let (inputs, outputs) = shape.clone().take_inputs_and_outputs();
    assert_eq!(inputs.len(), 2);
    assert_eq!(outputs.len(), 1);

    let edges: Vec<_> = shape.edges().collect();
    assert_eq!(edges.len(), 1, "only arg0->result, not arg1->result");
    assert_eq!(*edges[0].input().base(), 0, "edge comes from arg0");
    assert_eq!(edges[0].output().base(), ArgIdxOrResult::Result);
}

/// Single lifetime: both args flow to result.
#[test]
fn test_choose_single_lifetime() {
    let input = r#"
        fn caller() {
            let mut a = 0u32;
            let mut b = 0u32;
            let _r = choose(&mut a, &mut b);
        }

        fn choose<'a>(x: &'a mut u32, y: &'a mut u32) -> &'a mut u32 { x }
    "#;
    run_pcg_on_str(input, |analysis| {
        let (sig_shape, _) = sig_and_call_shapes(analysis.ctxt(), "choose");
        assert_choose_shape(&sig_shape);
    });
}

/// `'b: 'a` means arg1|'b also outlives result|'a, so both args flow to result.
#[test]
fn test_choose_two_lifetimes_with_outlives() {
    let input = r#"
        fn caller() {
            let mut a = 0u32;
            let mut b = 0u32;
            let _r = choose(&mut a, &mut b);
        }

        fn choose<'a, 'b: 'a>(x: &'a mut u32, y: &'b mut u32) -> &'a mut u32 { x }
    "#;
    run_pcg_on_str(input, |analysis| {
        let (sig_shape, _) = sig_and_call_shapes(analysis.ctxt(), "choose");
        assert_choose_shape(&sig_shape);
    });
}

/// No outlives constraint: only arg0 flows to result.
#[test]
fn test_choose_no_outlives() {
    let input = r#"
        fn caller() {
            let mut a = 0u32;
            let mut b = 0u32;
            let _r = choose(&mut a, &mut b);
        }

        fn choose<'a, 'b>(x: &'a mut u32, y: &'b mut u32) -> &'a mut u32 { x }
    "#;
    run_pcg_on_str(input, |analysis| {
        let (sig_shape, _) = sig_and_call_shapes(analysis.ctxt(), "choose");
        assert_choose_no_outlives_shape(&sig_shape);
    });
}

/// Even when the caller passes two refs with the same lifetime `'r`, the
/// sig-derived shape should still only connect arg0 to result.
#[test]
fn test_choose_no_outlives_caller_same_lifetime() {
    let input = r#"
        fn caller<'r>(r1: &'r mut u32, r2: &'r mut u32) {
            let _r = choose(r1, r2);
        }

        fn choose<'a, 'b>(x: &'a mut u32, y: &'b mut u32) -> &'a mut u32 { x }
    "#;
    run_pcg_on_str(input, |analysis| {
        let (sig_shape, _) = sig_and_call_shapes(analysis.ctxt(), "choose");
        assert_choose_no_outlives_shape(&sig_shape);
    });
}
