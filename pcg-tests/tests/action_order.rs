#![feature(rustc_private)]

//! The order of the actions at a location, which the annotations of the test
//! files do not check: a consumer applies them in this order.

use pcg::rustc_interface::middle::mir::BasicBlock;
use pcg_tests::{BodySelector, run_pcg_on_str};

/// The position of the first of `lines` that contains `needle`.
fn position(lines: &[String], needle: &str) -> usize {
    lines
        .iter()
        .position(|line| line.contains(needle))
        .unwrap_or_else(|| panic!("no action {needle} in {lines:#?}"))
}

/// When the loan of `(*x)@Some.0` ends, `*x` gets its record back and the
/// unpacking of `*x` to the variant, which only that loan needed, is
/// forgotten: the loan is removed before its layout.
#[test]
fn loan_removed_before_the_layout_it_frees() {
    let input = r#"
        pub fn f(x: &mut Option<(u32, u32)>, c: bool, d: &mut u32) {
            let mut r = d;
            if c {
                if let Some(p) = x {
                    r = &mut p.0;
                }
            }
            *r = 1;
            let _ = x.is_some();
        }
    "#;
    let recorder = pcg::CheckFailureRecorder::start();
    run_pcg_on_str(input, BodySelector::FirstFunction, true, |mut analysis| {
        let ctxt = analysis.results_ctxt();
        let lines = analysis
            .get_all_for_bb(BasicBlock::from(6_usize))
            .unwrap()
            .unwrap()
            .debug_lines(ctxt)
            .into_iter()
            .map(|line| line.into_owned())
            .filter(|line| line.starts_with("bb6[3] pre_operands: Remove Edge"))
            .collect::<Vec<_>>();
        let loan = position(&lines, "= &mut  (*x)@Some.0");
        let variant = position(&lines, "Remove Edge {(*x)@Some} -> {(*x)@Some.0}");
        let downcast = position(&lines, "Remove Edge {*x} -> {(*x)@Some}");
        assert!(
            loan < variant && variant < downcast,
            "the layout is forgotten before the loan ends: {lines:#?}"
        );
    });
    // The known violations in `f` (see `pcg::checks`).
    assert_eq!(
        recorder.finish(),
        ["frame", "label", "lend"]
            .map(|check| (check.to_owned(), "f".to_owned()))
            .into(),
        "the checks that fail in `f` changed"
    );
}
