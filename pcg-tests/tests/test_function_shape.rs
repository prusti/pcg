#![feature(rustc_private)]

use pcg::{
    borrow_pcg::{ArgIdxOrResult, FunctionShape},
    rustc_interface::middle::ty,
};
use pcg_tests::run_pcg_on_str;

#[test]
fn test_choose_shape() {
    let input = r#"
        fn choose<'a>(x: &'a mut u32, y: &'a mut u32) -> &'a mut u32 { x }
    "#;
    run_pcg_on_str(input, |analysis| {
        let ctxt = analysis.ctxt();
        let def_id = ctxt.def_id().to_def_id();
        let identity_substs = ty::GenericArgs::identity_for_item(ctxt.tcx(), def_id);
        let shape = FunctionShape::for_fn(def_id, identity_substs, ctxt).unwrap();

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
    });
}
