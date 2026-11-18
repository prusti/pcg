fn f<'a, 'b>(x: &'a mut Vec<&'b mut i32>, y: &'a mut Vec<&'b mut i32>) {
    let y_ref = y.pop().unwrap();
    // The future of `*y|13` shouldn't be blocked by an RP with a labelled place
    // ~PCG: bb0[4] post_main: *y↓'?13 FUTURE -> _5 after bb0[3]↓'?17

    // After `y.pop()`, `y` should be accessible again
    // ~PCG: bb1[1] post_main: y↓'?13 FUTURE -> *y↓'?13 FUTURE
    x.push(y_ref);
}

struct Wrap<'a, T> {
    inner: &'a mut T,
}

// Moving the reborrow of `**x` into `w` moves the future edge of its inner
// region `'b` to `w|'b`, not to `w|'a`: the borrow of `**x` then ends when `w`
// dies, and `**x` can be borrowed again.
fn moved_into_struct<'b>(x: &mut &mut &'b u32) {
    // PCG: bb0[3] post_main: Add Edge w↓'?13 -> **x↓'?11 FUTURE
    // ~PCG: bb0[3] post_main: Add Edge w↓'?12 -> **x↓'?11 FUTURE
    // PCG: bb0[7] pre_operands: Restore **x to E
    let w = Wrap { inner: *x };
    let _ = w;
    let _y = &mut **x;
}

fn main() {
}
