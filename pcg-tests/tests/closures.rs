#![feature(rustc_private)]

use pcg::{rustc_interface::middle::mir::START_BLOCK, utils::HasCompilerCtxt};
use pcg_tests::{BodySelector, run_pcg_on_str};

/// A closure body can be selected and analysed in its own right, rather than
/// only as part of the function that defines it.
#[test]
fn test_closure_body_is_analyzed() {
    let input = r#"
        fn outer(v: &mut i32) {
            let f = |y: &mut i32| {
                let z = &mut *y;
                *z += 1;
            };
            f(v);
        }
    "#;
    run_pcg_on_str(
        input,
        BodySelector::DefPath("outer::{closure#0}"),
        true,
        |mut analysis| {
            let ctxt = analysis.ctxt();
            assert_eq!(ctxt.ctxt().body_def_path_str(), "outer::{closure#0}");
            // The closure's own arguments: the closure environment, then `y`.
            assert_eq!(ctxt.body().arg_count, 2);
            assert!(
                analysis.get_all_for_bb(START_BLOCK).unwrap().is_some(),
                "the closure body should have been analysed"
            );
        },
    );
}
