#![feature(rustc_private)]

use std::collections::HashSet;

use pcg::{
    borrow_pcg::{
        ArgIdx, ArgIdxOrResult, FunctionShape,
        edge::abstraction::function::DefinedFnCallWithCallTys,
    },
    utils::{CompilerCtxt, HasCompilerCtxt},
};
use pcg_tests::run_pcg_on_str;

/// Extracts the `(DefId, GenericArgsRef)` for the first call to a function
/// whose name contains `target_name` in the given MIR body.
fn find_call<'a, 'tcx: 'a>(
    target_name: &str,
    ctxt: impl HasCompilerCtxt<'a, 'tcx>,
) -> DefinedFnCallWithCallTys<'tcx> {
    ctxt.body()
        .basic_blocks
        .iter()
        .find_map(|bb| {
            let term = bb.terminator();
            if let Some(defined_fn_call) =
                DefinedFnCallWithCallTys::from_terminator(term, ctxt.ctxt().def_id(), ctxt)
                && ctxt
                    .tcx()
                    .def_path_str(defined_fn_call.fn_def_id())
                    .contains(target_name)
            {
                return Some(defined_fn_call);
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
    let defined_fn_call = find_call(callee_name, ctxt);

    let sig_shape = FunctionShape::for_fn_sig(defined_fn_call.fn_def_id(), ctxt).unwrap();
    let call_shape = FunctionShape::for_fn_call(defined_fn_call, ctxt).unwrap();

    assert_eq!(
        sig_shape, call_shape,
        "sig-derived call shape should equal the sig shape.\n\nSig shape: {sig_shape}\n\nCall shape: {call_shape}\n"
    );

    (sig_shape, call_shape)
}

fn arg(idx: usize) -> ArgIdx {
    idx.into()
}

fn choose_shape() -> FunctionShape {
    FunctionShape::from_raw(
        vec![(arg(0), 0), (arg(1), 0)],
        vec![(ArgIdxOrResult::Result, 0)],
        HashSet::from([
            ((arg(0), 0), (ArgIdxOrResult::Result, 0)),
            ((arg(1), 0), (ArgIdxOrResult::Result, 0)),
        ]),
    )
}

fn choose_no_outlives_shape() -> FunctionShape {
    FunctionShape::from_raw(
        vec![(arg(0), 0), (arg(1), 0)],
        vec![(ArgIdxOrResult::Result, 0)],
        HashSet::from([((arg(0), 0), (ArgIdxOrResult::Result, 0))]),
    )
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
    run_pcg_on_str(input, true, |analysis| {
        let (sig_shape, _) = sig_and_call_shapes(analysis.ctxt(), "choose");
        assert_eq!(sig_shape, choose_shape());
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
    run_pcg_on_str(input, true, |analysis| {
        let (sig_shape, _) = sig_and_call_shapes(analysis.ctxt(), "choose");
        assert_eq!(sig_shape, choose_shape());
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
    run_pcg_on_str(input, true, |analysis| {
        let (sig_shape, _) = sig_and_call_shapes(analysis.ctxt(), "choose");
        assert_eq!(sig_shape, choose_no_outlives_shape());
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
    run_pcg_on_str(input, true, |analysis| {
        let (sig_shape, _) = sig_and_call_shapes(analysis.ctxt(), "choose");
        assert_eq!(sig_shape, choose_no_outlives_shape());
    });
}

/// `DerefMut::deref_mut` on `RefMut<'a, i32>` has an alias projection type
/// (`<RefMut<'a, i32> as Deref>::Target`) in its return type. The call-site
/// result type is `&mut i32` (1 region), so the shape uses the call-site types
/// for its structure. The `'a` region from `RefMut` cannot flow to the result
/// (which is just `i32`), so only the borrow lifetime connects to the result.
#[test]
fn test_deref_mut_alias_output() {
    let input = r#"
        use std::cell::RefCell;
        fn caller() {
            let cell = RefCell::new(42i32);
            let mut borrow = cell.borrow_mut();
            *borrow = 10;
        }
    "#;
    run_pcg_on_str(input, false, |analysis| {
        let ctxt = analysis.ctxt();
        let defined_fn_call = find_call("deref_mut", ctxt);
        let shape = FunctionShape::for_fn_call(defined_fn_call, ctxt).unwrap();

        let expected = FunctionShape::from_raw(
            vec![(arg(0), 0), (arg(0), 1)],
            vec![(ArgIdxOrResult::Result, 0)],
            HashSet::from([
                ((arg(0), 0), (ArgIdxOrResult::Result, 0)),
                ((arg(0), 1), (ArgIdxOrResult::Argument(arg(0)), 1)),
            ]),
        );
        assert_eq!(shape, expected);
    });
}

/// `Vec<&'a mut i32>::into_iter` should have a 1-to-1 shape: the single
/// region in the input (`'a` in `Vec<&'a mut i32>`) flows to the single
/// region in the result (`'a` in `IntoIter<&'a mut i32>`).
///
/// Note: the sig shape uses identity substs, where `T` is a type parameter
/// with no regions. The regions only appear with the caller's substs (where
/// `T = &'a mut i32`). This test checks the sig-derived call shape only.
#[test]
fn test_vec_into_iter_shape() {
    let input = r#"
        fn caller<'a>(v: Vec<&'a mut i32>) {
            let _iter = v.into_iter();
        }
    "#;
    run_pcg_on_str(input, true, |analysis| {
        let ctxt = analysis.ctxt();
        let defined_fn_call = find_call("into_iter", ctxt);
        let call_shape = FunctionShape::for_fn_call(defined_fn_call, ctxt).unwrap();

        let expected = FunctionShape::from_raw(
            vec![(arg(0), 0)],
            vec![(ArgIdxOrResult::Result, 0)],
            HashSet::from([((arg(0), 0), (ArgIdxOrResult::Result, 0))]),
        );
        assert_eq!(call_shape, expected);
    });
}
