#![feature(rustc_private)]
use pcg::visualization::graph_constructor::PcgGraphConstructor;
use pcg_tests::run_pcg_on_str;

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
    run_pcg_on_str(input, |mut analysis| {
        let bb = analysis.get_all_for_bb(0usize.into()).unwrap().unwrap();
        let ctxt = analysis.ctxt();
        let stmt = &bb.statements[22];
        let pcg = stmt.states.eval_stmt_data().post_main();
        let graph = PcgGraphConstructor::new(pcg.into(), ctxt, stmt.location).construct_graph();
        assert!(graph.has_edge_between_labelled_nodes("s", "s.x", ctxt));
    });
}
