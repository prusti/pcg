fn f(x: &mut &i32) {
    // PCG_LIFETIME_DISPLAY: x 0 'outer
    // PCG_LIFETIME_DISPLAY: x 1 'inner
    // Reading through `*x` must neither add future edges for `x` nor label
    // the lifetime projections of `x`.
    // ~PCG: bb2[2] pre_main: x↓'inner loop bb1 -> x↓'inner
    // ~PCG: bb2[2] pre_main: *x before bb1[0]:PreOperands↓'inner -> x↓'inner
    // ~PCG: bb2[2] pre_main: Remote(_1)↓'outer -> x↓'outer loop bb1
    // PCG: bb2[2] pre_main: Remote(_1)↓'outer -> x↓'outer
    // PCG: bb2[2] pre_main: {x↓'inner} -> {*x before bb2[2]:PreOperands↓'inner}
    // Once the borrow held by `_r` is dead, `_r` retains only W.
    // PCG: bb2[3] pre_operands: Weaken _r from E to W
    // PCG: bb2[3] pre_operands: _r: W
    loop {
        let _r = *x;
    }
}

fn main() {}
