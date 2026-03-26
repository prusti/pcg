#![feature(rustc_private)]

use pcg::{
    borrow_pcg::{
        ArgIdxOrResult, FunctionShape,
        edge::abstraction::function::DefinedFnCallWithCallTys,
    },
    utils::{CompilerCtxt, HasCompilerCtxt},
};
use pcg_tests::run_pcg_on_str;

/// Returns the [`DefinedFnCallWithCallTys`] for the first call to a function
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

// ---------------------------------------------------------------------------
// Shape construction helpers
//
// A *node* is a (base, region_index) pair written as `arg(i, r)` or `result(r)`.
// An *edge* is `arg(i, r) => result(r)` or `arg(i, r) => arg(j, r)`.
// ---------------------------------------------------------------------------

type Node = (ArgIdxOrResult, usize);

fn arg(idx: usize, region: usize) -> Node {
    (ArgIdxOrResult::Argument(idx.into()), region)
}

fn result(region: usize) -> Node {
    (ArgIdxOrResult::Result, region)
}

/// Constructs a [`FunctionShape`] from a list of input nodes, output nodes,
/// and edges. Each node is created via [`arg`] or [`result`].
fn make_shape(inputs: &[Node], outputs: &[Node], edges: &[(Node, Node)]) -> FunctionShape {
    let inputs = inputs
        .iter()
        .map(|(base, region)| {
            let ArgIdxOrResult::Argument(idx) = base else {
                panic!("inputs must be arguments, not result");
            };
            (*idx, *region)
        })
        .collect();
    let outputs = outputs.iter().copied().collect();
    let edges = edges
        .iter()
        .map(|((in_base, in_r), out)| {
            let ArgIdxOrResult::Argument(idx) = in_base else {
                panic!("edge source must be an argument, not result");
            };
            ((*idx, *in_r), *out)
        })
        .collect();
    FunctionShape::from_raw(inputs, outputs, edges)
}

fn choose_shape() -> FunctionShape {
    make_shape(
        &[arg(0, 0), arg(1, 0)],
        &[result(0)],
        &[
            (arg(0, 0), result(0)),
            (arg(1, 0), result(0)),
        ],
    )
}

fn choose_no_outlives_shape() -> FunctionShape {
    make_shape(
        &[arg(0, 0), arg(1, 0)],
        &[result(0)],
        &[(arg(0, 0), result(0))],
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
/// for its structure. The `'a` region from `RefMut` could flow to the result
/// (the deref returns data borrowed through `'a`), so both arg regions connect
/// to the result.
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

        let expected = make_shape(
            &[arg(0, 0), arg(0, 1)],
            &[result(0)],
            &[
                (arg(0, 0), result(0)),
                (arg(0, 1), arg(0, 1)),
            ],
        );
        assert_eq!(shape, expected);
    });
}

/// `Vec<&'a mut i32>::into_iter` should have a 1-to-1 shape: the single
/// region in the input (`'a` in `Vec<&'a mut i32>`) flows to the single
/// region in the result (`'a` in `IntoIter<&'a mut i32>`).
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

        let expected = make_shape(
            &[arg(0, 0)],
            &[result(0)],
            &[(arg(0, 0), result(0))],
        );
        assert_eq!(call_shape, expected);
    });
}
