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

struct T<'a> {
    n: i32,
    r: &'a i32,
}

fn set<'a>(r: &mut &'a i32, y: &'a i32) {
    *r = y;
}

// Borrowing `t.n` expands `t` without changing `t`'s `'a`; the call then
// changes `t.r` through the same expansion, so the returned `t` is blocked
// by `y`.
fn write_after_sibling_borrow<'a>(mut t: T<'a>, y: &'a i32) -> T<'a> {
    let n = &mut t.n;
    set(&mut t.r, y);
    *n += 1;
    // PCG: bb2[3] post_main: aggregate {t.r before bb2[1]:PreOperands↓'?9} -> t before bb2[1]:PostOperands↓'?9
    t
}

// As `write_after_sibling_borrow`, through a reference and with the write in
// a loop: the borrow of `t.n` leaves `*t`'s `'a` unlabelled, and the join at
// the loop head must stay valid.
fn write_in_loop_after_sibling_borrow<'a>(t: &mut T<'a>, y: &'a i32, k: i32) {
    let n = &mut t.n;
    let mut i = 0;
    while i < k {
        t.r = y;
        i += 1;
    }
    *n += 1;
}

// A loop that writes a field without references before one with a reference:
// the write of `t.n` leaves `*t`'s `'a` unlabelled, and the join at the loop
// head must stay valid.
fn write_fields_in_loop<'a>(t: &mut T<'a>, y: &'a i32, k: i32) {
    let mut i = 0;
    while i < k {
        t.n += 1;
        t.r = y;
        i += 1;
    }
}

trait Slice {
    fn slice(&self) -> &[u8];
}

struct U<A> {
    d: A,
    n: usize,
    e: A,
}

// The mutable borrows of `u.e` reuse the expansion of `*u` while `u.d` is
// borrowed shared; the capabilities of `u` and its fields must pass the
// validity checks.
fn borrow_sibling_of_shared<A: Slice>(u: &mut U<A>, k: usize) -> usize {
    let d = if u.n > k {
        let d = u.d.slice();
        u.n = k;
        d
    } else {
        u.d.slice()
    };
    let _ = &mut u.e;
    let _ = &mut u.e;
    d.len()
}

struct V<'a> {
    n: i32,
    d: i32,
    r: &'a i32,
}

// As `write_after_sibling_borrow`, while another sibling is borrowed shared.
fn write_while_sibling_borrowed<'a>(mut v: V<'a>, y: &'a i32) -> V<'a> {
    let n = &mut v.n;
    let d = &v.d;
    set(&mut v.r, y);
    *n += *d;
    // PCG: bb2[5] post_main: aggregate {v.r before bb2[1]:PreOperands↓'?10} -> v before bb2[2]:PostOperands↓'?10
    v
}

// The write labels the old `t.r` before the expansion of `*t` is labelled;
// the future of `*t` must be made of the new `t.r`, which holds `y`.
fn write_then_read_after_sibling_borrow<'a>(t: &mut T<'a>, y: &'a i32) -> &'a i32 {
    let n = &mut t.n;
    t.r = y;
    *n += 1;
    // PCG: bb1[2] post_main: _4 before bb0[5]:PostOperands↓'?12 -> (*t).r↓'?9 before bb1[1]:PreOperands
    t.r
}

// `t.r` changes on one path only; collapsing `t` must keep `y`'s flow.
fn write_on_one_path<'a>(mut t: T<'a>, y: &'a i32, c: bool) -> T<'a> {
    let n = &mut t.n;
    if c {
        t.r = y;
    }
    *n += 1;
    // PCG: bb4[3] post_main: aggregate {t.r before bb4[1]:PreOperands↓'?6} -> t before bb4[1]:PostOperands↓'?6
    t
}

struct W<'a> {
    n: i32,
    m: i32,
    r: &'a i32,
}

// One path borrows a field mutably, the other reads one; the write after the
// join changes `*w`'s `'a` on both, so the returned `w.r` comes from `y`.
fn write_after_mixed_borrows<'a>(w: &mut W<'a>, y: &'a i32, c: bool) -> &'a i32 {
    let z = 0;
    let mut v = 0;
    let n: &mut i32;
    let k: &i32;
    if c {
        n = &mut w.n;
        k = &z;
    } else {
        n = &mut v;
        k = &w.m;
    }
    w.r = y;
    *n += *k;
    // PCG: bb4[7] post_main: _18 before bb3[4]:PostOperands↓'?28 -> (*w).r↓'?16 before bb4[1]:PreOperands
    w.r
}

struct X<'a> {
    n: i32,
    t: T<'a>,
}

// One path borrows a field mutably, the other reads `x.t.r`'s referent, which
// stays borrowed across the write: the write must not leave a current version
// of `(*x).t`'s projection next to its placeholder.
fn write_while_read_on_one_path<'a>(x: &mut X<'a>, y: &'a i32, c: bool) {
    let k: &'a i32;
    if c {
        let n = &mut x.t.n;
        *n += 1;
        k = y;
    } else {
        k = &*x.t.r;
    }
    x.t.r = y;
    let _ = *k;
}

// One path borrows a field mutably, the other reads `w.r`'s referent; the
// write upgrades the read and must connect the new `w.r` to the future of
// `*w`.
fn write_after_read_on_one_path<'a>(w: &mut W<'a>, y: &'a i32, c: bool) -> &'a i32 {
    let k: &'a i32;
    if c {
        let n = &mut w.n;
        *n += 1;
        k = y;
    } else {
        k = &*w.r;
    }
    w.r = y;
    // PCG: bb4[4] post_main: (*w).r↓'?11 -> *w↓'?11 FUTURE
    k
}

enum E<'a> {
    A(i32, &'a i32),
    B(&'a i32),
}

// Every path into the `if let` reborrows a reference under `*e`, so only the
// placeholder of `*e`'s `'a` is left; expanding `*e` again for `n` must not
// bring back a current version of it.
fn expand_after_reborrows_on_all_paths<'a>(e: &mut E<'a>) -> &'a i32 {
    let k = match e {
        E::A(_, r) => *r,
        E::B(r) => *r,
    };
    if let E::A(n, _) = e {
        *n += 1;
    }
    k
}

struct Y<'a> {
    v: Vec<&'a u32>,
    n: usize,
}

// The two-phase borrow of `y.v` for `push` is reserved while `y.n` is
// borrowed shared, so `y` keeps its read capability until the activation.
fn push_while_sibling_borrowed<'a>(y: &mut Y<'a>, x: &'a u32) {
    let n = &y.n;
    // PCG: bb0[8] pre_operands: Weaken y from R to e
    y.v.push(x);
    let _ = *n;
}

struct G<I: Iterator> {
    it: I,
    cur: Option<I::Item>,
    n: u32,
}

// `cur`'s type normalizes to `Option<&'a mut i32>`, so `cur` is a part of
// `*g`'s projection for `'a`, and the write of `y` flows into it.
fn write_alias_field<'a>(g: &mut G<std::slice::IterMut<'a, i32>>, y: &'a mut i32) {
    g.cur = Some(y);
    // PCG: bb0[5] post_main: _3 before bb0[5]:PostOperands↓'?10 -> (*g).cur↓'?8
    // PCG: bb0[5] post_main: (*g).cur↓'?8 -> *g↓'?8 FUTURE
}

// As `write_alias_field`, after a write of a sibling without references: the
// write of `n` leaves `*g`'s `'a` unlabelled, and the write of `cur` must label
// it, so `g`'s future comes from `*g`'s.
fn write_alias_field_after_sibling_write<'a>(g: &mut G<std::slice::IterMut<'a, i32>>, y: &'a mut i32) {
    g.n += 1;
    g.cur = Some(y);
    // PCG: bb1[6] post_main: *g↓'?8 FUTURE -> g↓'?8 FUTURE
}

// Borrowing `cur` borrows the `&'a mut i32` it holds, which the borrow's
// projection for `'a` receives from `cur`'s.
fn write_through_alias_field<'a>(g: &mut G<std::slice::IterMut<'a, i32>>) {
    if let Some(r) = &mut g.cur {
        // PCG: bb0[1] post_main: (*g).cur↓'?9 before bb0[1]:PostMain -> _2↓'?11
        **r += 1;
    }
}

// The bound on `I` gives `cur` the type `Option<&'a mut i32>`, but `G<I>` has
// no `'a`, so the write may change every projection of `*g`.
fn write_bound_alias_field<'a, I: Iterator<Item = &'a mut i32>>(g: &mut G<I>, y: &'a mut i32) {
    g.n += 1;
    g.cur = Some(y);
    // PCG: bb1[6] post_main: *g↓RegionsIn(I) FUTURE -> g↓RegionsIn(I) FUTURE
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

// As `write_through_closure_capture`, in an `FnMut` closure that borrows another
// capture across the write: the borrow of `v` leaves the projections of `x`'s
// capture unlabelled, and the write of `x.r` must label the closure's
// projection for `'a`, so `_1`'s future comes from `*_1`'s.
fn write_through_closure_capture_in_loop<'a>(x: &mut H<'a>, ys: Vec<&'a mut i32>, mut v: Vec<u8>) -> usize {
    let mut f = move |y: &'a mut i32| -> usize {
        let k = &mut v;
        k.push(1);
        x.r = y;
        // PCG: bb1[4] post_main: (*_1)↓'?20 FUTURE -> _1↓'?20 FUTURE
        k.len()
    };
    let mut s = 0;
    for y in ys {
        s += f(y);
    }
    s
}

union Un<'a, 'b> {
    a: &'a i32,
    b: &'b i32,
}

// Union fields share storage, so writing `a` may change every projection of
// `*u`.
fn write_union_field<'a, 'b>(u: &mut Un<'a, 'b>, y: &'a i32) -> &'b i32 {
    unsafe {
        (*u).a = y;
        // PCG: bb0[2] post_main: *u↓'?10 FUTURE -> u↓'?10 FUTURE
        (*u).b
    }
}
