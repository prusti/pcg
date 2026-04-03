#![feature(rustc_private)]

use pcg::{
    borrow_pcg::{
        ArgIdx, ArgIdxOrResult, FunctionShape,
        edge::abstraction::function::DefinedFnCallWithCallTys, region_projection::Generalized,
    },
    utils::{CompilerCtxt, HasCompilerCtxt},
    visualization::mir_graph::ShapeLabelFormatter,
};

type SigShape = FunctionShape<Generalized>;
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

/// Builds the sig shape (generalized lifetime projections) and call shape
/// (lifetime projections) for a callee found in the current body, and asserts
/// they have the same Display representation (valid when the function has no
/// type parameters).
fn sig_and_call_shapes<'a, 'tcx: 'a>(
    ctxt: CompilerCtxt<'a, 'tcx>,
    callee_name: &str,
) -> FunctionShape {
    let defined_fn_call = find_call(callee_name, ctxt);

    let sig_shape: SigShape = SigShape::for_fn_sig(defined_fn_call.fn_def_id(), ctxt).unwrap();
    let call_shape: FunctionShape = FunctionShape::for_fn_call(defined_fn_call, ctxt).unwrap();

    let sig_str = sig_shape.to_string();
    let call_str = call_shape.to_string();
    assert_eq!(
        sig_str, call_str,
        "sig-derived shape should equal the call shape.\n\nSig shape: {sig_str}\n\nCall shape: {call_str}\n"
    );

    call_shape
}

// ---------------------------------------------------------------------------
// Shape comparison with detailed diff output
// ---------------------------------------------------------------------------

use pcg::borrow_pcg::{
    FunctionShapeInput, FunctionShapeOutput, edge::abstraction::AbstractionBlockEdge,
    region_projection::RegionIdxKind,
};

type Edge<Kind> =
    AbstractionBlockEdge<'static, FunctionShapeInput<Kind>, FunctionShapeOutput<Kind>>;

/// Formats a function shape input node, using the formatter for pretty labels
/// when available, otherwise falling back to the raw `Display` representation.
fn format_input<Kind: RegionIdxKind>(
    input: &FunctionShapeInput<Kind>,
    formatter: Option<&ShapeLabelFormatter>,
) -> String {
    match formatter {
        Some(f) => {
            let pretty = f.format_input(input);
            format!("{input} ({pretty})")
        }
        None => format!("{input}"),
    }
}

/// Formats a function shape output node, using the formatter for pretty labels
/// when available, otherwise falling back to the raw `Display` representation.
fn format_output<Kind: RegionIdxKind>(
    output: &FunctionShapeOutput<Kind>,
    formatter: Option<&ShapeLabelFormatter>,
) -> String {
    match formatter {
        Some(f) => {
            let pretty = f.format_output(output);
            format!("{output} ({pretty})")
        }
        None => format!("{output}"),
    }
}

/// Formats an edge using the formatter for pretty labels when available.
fn format_edge<Kind: RegionIdxKind>(
    edge: &Edge<Kind>,
    formatter: Option<&ShapeLabelFormatter>,
) -> String {
    match formatter {
        Some(f) => {
            let input = f.format_input(&edge.input());
            let output = f.format_output(&edge.output());
            format!("{input} -> {output}")
        }
        None => format!("{edge}"),
    }
}

/// Asserts that `actual` equals `expected`, printing a human-readable diff of
/// inputs, outputs, and edges on failure. When a [`ShapeLabelFormatter`] is
/// provided, nodes are annotated with visualization-style names (e.g.
/// `self↓'a`).
fn assert_shape_eq_with_formatter<Kind: RegionIdxKind>(
    actual: &FunctionShape<Kind>,
    expected: &FunctionShape<Kind>,
    formatter: Option<&ShapeLabelFormatter>,
) {
    if actual == expected {
        return;
    }

    let (actual_inputs, actual_outputs) = actual.clone().take_inputs_and_outputs();
    let (expected_inputs, expected_outputs) = expected.clone().take_inputs_and_outputs();

    let actual_edges: Vec<Edge<Kind>> = actual.edges().collect();
    let expected_edges: Vec<Edge<Kind>> = expected.edges().collect();

    let missing: Vec<&Edge<Kind>> = expected_edges
        .iter()
        .filter(|e| !actual_edges.contains(e))
        .collect();
    let extra: Vec<&Edge<Kind>> = actual_edges
        .iter()
        .filter(|e| !expected_edges.contains(e))
        .collect();

    let fmt_inputs = |inputs: &[FunctionShapeInput<Kind>]| -> String {
        let items: Vec<String> = inputs.iter().map(|n| format_input(n, formatter)).collect();
        format!("Inputs: [{}]", items.join(", "))
    };
    let fmt_outputs = |outputs: &[FunctionShapeOutput<Kind>]| -> String {
        let items: Vec<String> = outputs
            .iter()
            .map(|n| format_output(n, formatter))
            .collect();
        format!("Outputs: [{}]", items.join(", "))
    };

    let mut msg = String::new();
    msg.push_str("function shapes differ\n");
    msg.push_str(&format!(
        "\n--- Expected ---\n{}\n{}\n",
        fmt_inputs(&expected_inputs),
        fmt_outputs(&expected_outputs),
    ));
    msg.push_str("Edges:\n");
    for e in &expected_edges {
        msg.push_str(&format!("  {}\n", format_edge(e, formatter)));
    }
    msg.push_str(&format!(
        "\n--- Actual ---\n{}\n{}\n",
        fmt_inputs(&actual_inputs),
        fmt_outputs(&actual_outputs),
    ));
    msg.push_str("Edges:\n");
    for e in &actual_edges {
        msg.push_str(&format!("  {}\n", format_edge(e, formatter)));
    }
    if !missing.is_empty() {
        msg.push_str("\nMissing edges (in expected, not in actual):\n");
        for e in &missing {
            msg.push_str(&format!("  - {}\n", format_edge(e, formatter)));
        }
    }
    if !extra.is_empty() {
        msg.push_str("\nExtra edges (in actual, not in expected):\n");
        for e in &extra {
            msg.push_str(&format!("  + {}\n", format_edge(e, formatter)));
        }
    }
    panic!("{msg}");
}

/// Asserts that `actual` equals `expected`, printing a human-readable diff of
/// inputs, outputs, and edges on failure.
fn assert_shape_eq<Kind: RegionIdxKind>(
    actual: &FunctionShape<Kind>,
    expected: &FunctionShape<Kind>,
) {
    assert_shape_eq_with_formatter(actual, expected, None);
}

// ---------------------------------------------------------------------------
// Shape construction helpers
//
// A *node* is a (base, region_index) pair written as `arg(i, r)` or `result(r)`.
// An *edge* is `arg(i, r) => result(r)` or `arg(i, r) => arg(j, r)`.
// ---------------------------------------------------------------------------

type InputNode = (ArgIdx, usize);
type OutputNode = (ArgIdxOrResult, usize);

fn arg_in(idx: usize, region: usize) -> InputNode {
    (idx.into(), region)
}

fn arg_out(idx: usize, region: usize) -> OutputNode {
    (ArgIdxOrResult::Argument(idx.into()), region)
}

fn result(region: usize) -> OutputNode {
    (ArgIdxOrResult::Result, region)
}

/// Constructs a [`SigShape`] from typed input/output nodes and edges.
fn make_sig_shape(
    inputs: &[InputNode],
    outputs: &[OutputNode],
    edges: &[(InputNode, OutputNode)],
) -> SigShape {
    SigShape::from_raw(
        inputs.to_vec(),
        outputs.to_vec(),
        edges.iter().copied().collect(),
    )
}

/// Constructs a [`FunctionShape`] from typed input/output nodes and edges.
fn make_shape(
    inputs: &[InputNode],
    outputs: &[OutputNode],
    edges: &[(InputNode, OutputNode)],
) -> FunctionShape {
    FunctionShape::from_raw(
        inputs.to_vec(),
        outputs.to_vec(),
        edges.iter().copied().collect(),
    )
}

fn choose_shape() -> FunctionShape {
    make_shape(
        &[arg_in(0, 0), arg_in(1, 0)],
        &[result(0)],
        &[(arg_in(0, 0), result(0)), (arg_in(1, 0), result(0))],
    )
}

fn choose_no_outlives_shape() -> FunctionShape {
    make_shape(
        &[arg_in(0, 0), arg_in(1, 0)],
        &[result(0)],
        &[(arg_in(0, 0), result(0))],
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
        let call_shape = sig_and_call_shapes(analysis.ctxt(), "choose");
        assert_shape_eq(&call_shape, &choose_shape());
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
        let call_shape = sig_and_call_shapes(analysis.ctxt(), "choose");
        assert_shape_eq(&call_shape, &choose_shape());
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
        let call_shape = sig_and_call_shapes(analysis.ctxt(), "choose");
        assert_shape_eq(&call_shape, &choose_no_outlives_shape());
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
        let call_shape = sig_and_call_shapes(analysis.ctxt(), "choose");
        assert_shape_eq(&call_shape, &choose_no_outlives_shape());
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
            &[arg_in(0, 0), arg_in(0, 1)],
            &[result(0)],
            &[
                (arg_in(0, 0), result(0)),
                (arg_in(0, 1), arg_out(0, 1)),
                (arg_in(0, 1), result(0)),
            ],
        );
        assert_shape_eq(&shape, &expected);
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

        let expected = make_shape(&[arg_in(0, 0)], &[result(0)], &[(arg_in(0, 0), result(0))]);
        assert_shape_eq(&call_shape, &expected);
    });
}

#[test]
fn test_tricky() {
    let input = r#"
fn caller() {
    let mut i = 42;
    let mut a = A {
        f: &mut i,
    };
    let b = a.get::<&mut i32>();
    *b = 1;
}

trait Foo<'a> {
    fn get<'b, T: FromMutref<'b>>(&'b mut self) -> T;
}

struct A<'a> {
    f: &'a mut i32,
}

impl<'a> Foo<'a> for A<'a> {
    fn get<'b, T: FromMutref<'b>>(&'b mut self) -> T {
        T::from_mutref(&mut self.f)
    }
}

trait FromMutref<'a> {
    fn from_mutref(x: &'a mut i32) -> Self;
}

impl<'a> FromMutref<'a> for &'a mut i32 {
    fn from_mutref(x: &'a mut i32) -> Self { x }
}
    "#;
    run_pcg_on_str(input, true, |analysis| {
        let ctxt = analysis.ctxt();
        let call = find_call("get", ctxt); // Call to `get()` in `caller()`
        let sig_shape = SigShape::for_fn_sig(call.fn_def_id(), ctxt).unwrap();
        // arg_in(0,0) = 'b, arg_in(0,1) = RegionsIn(Self), arg_in(0,2) = 'a (from Self: Foo<'a>)
        // result(0) = RegionsIn(T), result(1) = 'b (from T: FromMutref<'b>),
        // result(2) = 'a (all sig lifetimes included for type param result)
        //
        // Key edges and their derivations:
        //
        //   self|'b → result|'b:
        //     'b outlives 'b (reflexive).
        //
        //   self|RegionsIn(Self) → self|RegionsIn(Self):
        //     Reflexive; RegionsIn(Self) is invariant in &'b mut Self.
        //
        //   self|RegionsIn(Self) → result|'b:
        //     RegionsIn(Self) → Region('b) (implied bound from &'b mut Self).
        //
        //   self|'a → result|'a:
        //     'a outlives 'a (reflexive). The result includes 'a because T is
        //     a type parameter and could contain borrows under any signature
        //     lifetime.

        let self_b = arg_in(0, 0);
        let regions_in_self = arg_in(0, 1);
        let self_a = arg_in(0, 2);
        let regions_in_self_out = arg_out(0, 1);
        let regions_in_result = result(0);
        let result_b = result(1);
        let result_a = result(2);

        let formatter = ShapeLabelFormatter::for_fn_sig(call.fn_def_id(), ctxt.tcx());

        let expected = make_sig_shape(
            &[self_b, regions_in_self, self_a],
            &[regions_in_result, result_b, result_a],
            &[
                (self_b, result_b),
                (regions_in_self, regions_in_self_out),
                (regions_in_self, result_b),
                (self_a, result_a),
            ],
        );
        assert_shape_eq_with_formatter(&sig_shape, &expected, Some(&formatter));
    })
}
