//! Regression for prusti/pcg#137: unsound restoration to `E` after
//! expiry of a conditional borrow whose blocked place was moved out
//! on one incoming path.
//!
//! Scenario: we borrow `p` on the `else` branch and `p2` on the `if`
//! branch (and move the other one out). After the join, both `p` and
//! `p2` have been conditionally moved. When `rp` expires, the old
//! rule "mutable borrow to `p` dies, restore to Exclusive" gave `p`
//! capability `E` even though it was moved out on one incoming path
//! — that's the bug fixed by driving owned-place capabilities from
//! the initialisation state.

fn consume(_: String) {}

fn conditional_move_2(choice: bool) {
    let mut p = String::new();
    let mut p2 = String::new();
    let rp: &mut String = if choice {
        consume(p);
        &mut p2
    } else {
        consume(p2);
        &mut p
    };
    *rp = String::from("updated");
    // After the borrow expires, neither `p` nor `p2` may have `E`
    // capability: each was moved out on one incoming path, so the
    // initialisation state joins to `Uninit` and the computed
    // capability is `W`.
    // PCG: bb9[1] post_main: p: W
    // PCG: bb9[1] post_main: p2: W
    // ~PCG: bb9[1] post_main: p: E
    // ~PCG: bb9[1] post_main: p2: E
}

fn main() {
    conditional_move_2(false);
}
