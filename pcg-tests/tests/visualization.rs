#![feature(rustc_private)]
use pcg::visualization::graph_constructor::PcgGraphConstructor;
use pcg_tests::{BodySelector, run_pcg_on_str};

// 26_ref_in_struct.rs
#[test]
fn test_expand_created() {
    let input = r#"
    struct S<'a> {
x: &'a mut i32,
y: &'a mut i32,
}

fn main() {
let mut x = 1;
let mut y = 2;
let s = S { x: &mut x, y: &mut y };
let rx = s.x;
*rx = 1;
}
"#;
    run_pcg_on_str(input, BodySelector::FirstFunction, true, |mut analysis| {
        let bb = analysis.get_all_for_bb(0usize.into()).unwrap().unwrap();
        let ctxt = analysis.ctxt();
        let stmt = &bb.statements[22];
        let pcg = stmt.states.eval_stmt_data().post_main();
        let graph = PcgGraphConstructor::new(pcg.into(), ctxt, stmt.location).construct_graph();
        assert!(graph.has_edge_between_labelled_nodes("s", "s.x", ctxt));
    });
}

#[test]
fn svg_preserves_hyperedge_membership() {
    let input = r#"
fn example(pair: &mut (i32, i32)) {
    let r: &mut (i32, i32) = &mut *pair;
    r.0 = 1;
    r.1 = 2;
}
"#;
    run_pcg_on_str(input, BodySelector::FirstFunction, true, |mut analysis| {
        let bb = analysis.get_all_for_bb(0usize.into()).unwrap().unwrap();
        let ctxt = analysis.ctxt();
        let mut saw_deref = false;
        let mut saw_unpack = false;
        for stmt in &bb.statements {
            let pcg = stmt.states.eval_stmt_data().post_main();
            let graph = PcgGraphConstructor::new(pcg.into(), ctxt, stmt.location).construct_graph();
            let hypergraph = graph.to_hypergraph(ctxt);
            for edge in &hypergraph.edges {
                if edge.sources.len() == 2 && edge.targets.len() == 1 {
                    assert!(edge.label.is_empty());
                    saw_deref = true;
                }
                if edge.sources.len() == 1 && edge.targets.len() == 2 {
                    assert!(edge.label.is_empty());
                    saw_unpack = true;
                }
            }
            let svg = hypergraph.to_svg().unwrap();
            assert_eq!(
                svg.matches("class=\"node\"").count(),
                hypergraph.nodes.len()
            );
        }
        assert!(
            saw_deref,
            "expected a reference and its lifetime projection as deref sources"
        );
        assert!(saw_unpack, "expected both tuple fields in one target set");
    });
}
