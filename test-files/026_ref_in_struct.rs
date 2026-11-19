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

struct G<I: Iterator> {
    it: I,
    cur: Option<I::Item>,
}

// `cur`'s type normalizes to `Option<&'a mut i32>`, so `cur` is a part of
// `*g`'s projection for `'a`, and the write of `y` flows into it.
fn write_alias_field<'a>(g: &mut G<std::slice::IterMut<'a, i32>>, y: &'a mut i32) {
    g.cur = Some(y);
    // PCG: bb0[5] post_main: _3 before bb0[5]:PostOperands↓'?10 -> (*g).cur↓'?8
    // PCG: bb0[5] post_main: (*g).cur↓'?8 -> *g↓'?8 FUTURE
}

// Borrowing `cur` borrows the `&'a mut i32` it holds, which the borrow's
// projection for `'a` receives from `cur`'s.
fn write_through_alias_field<'a>(g: &mut G<std::slice::IterMut<'a, i32>>) {
    if let Some(r) = &mut g.cur {
        // PCG: bb0[1] post_main: (*g).cur↓'?9 before bb0[1]:PostMain -> _2↓'?11
        **r += 1;
    }
}

struct H<'a> {
    r: &'a mut i32,
}

// `(*_1).0` (the captured `x`) takes its type from the closure's upvar types,
// not from the MIR projection, so the write through it flows into the
// closure's projection for `'a`.
fn write_through_closure_capture<'a>(x: &mut H<'a>, y: &'a mut i32) {
    let mut f = move |y: &'a mut i32| {
        x.r = y;
        // PCG: bb0[2] post_main: _3 before bb0[2]:PostOperands↓'?19 -> (*(*_1).0).0↓'?17
        // PCG: bb0[2] post_main: (*_1).0↓'?17 FUTURE -> (*_1)↓'?17 FUTURE
    };
    f(y);
}
