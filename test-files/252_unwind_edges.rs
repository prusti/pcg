// A call that unwinds does not assign its destination, but its callee may have
// used its arguments: on the edge to the cleanup block, the destination is
// still uninitialised, and the call abstraction is introduced as when the call
// returns. Its edges into the result, which is never assigned, expire on the
// edge, and so do the borrows passed to the call.

fn g(x: &mut u32) -> u32 {
    *x
}

fn returns_value(x: &mut u32, b: Box<u32>) -> u32 {
    let r = g(&mut *x);
    // PCG: bb0[5] post_main: r: E
    // PCG: bb4[0] pre_main: r: W
    // ~PCG: bb4[0] pre_main: r: E
    // PCG: bb0 -> bb4: Remove Edge borrow: _5 = &mut  *x
    r + *b
}

fn h<'a>(x: &'a mut u32) -> &'a mut u32 {
    x
}

fn returns_reborrow(x: &mut u32, b: Box<u32>) {
    let r = h(x);
    // PCG: bb0[3] post_main: r: E
    // PCG: bb3[0] pre_operands: r: W
    // PCG: bb0 -> bb3: Add Edge call h at bb0[3]: _4 before bb0[3]:PostOperands↓'?6 before bb0[3]:PostMain -> r↓'?5
    // PCG: bb0 -> bb3: Remove Edge call h at bb0[3]: _4 before bb0[3]:PostOperands↓'?6 before bb0[3]:PostMain -> r↓'?5
    // PCG: bb0 -> bb3: Remove Edge borrow: _4 before bb0[3]:PostOperands <before bb0[3]:PostMain> = &mut  *x
    // ~PCG: bb3[0] pre_operands: call h at bb0[3]: _4 before bb0[3]:PostOperands↓'?6 before bb0[3]:PostMain -> r↓'?5 under conditions bb0 -> bb3
    *r = *b;
}

pub struct Wrapper<'a>(&'a mut u32);

fn wrap<'a>(x: &'a mut u32) -> Wrapper<'a> {
    Wrapper(x)
}

// The result of `wrap` is the return place, which a function that unwinds
// abandons: its borrow of `*x` ends on the edge where `wrap` unwinds, and on
// the edge where dropping `b` unwinds after the return place is assigned.
fn returns_call_result<'a>(x: &'a mut u32, b: Box<u32>) -> Wrapper<'a> {
    wrap(x)
    // PCG: bb0 -> bb3: Remove Edge call wrap at bb0[2]: _3 before bb0[2]:PostOperands↓'?6 before bb0[2]:PostMain -> RETURN↓'?4
    // PCG: bb1 -> bb4: Remove Edge call wrap at bb0[2]: _3 before bb0[2]:PostOperands↓'?6 before bb0[2]:PostMain -> RETURN↓'?4 under conditions bb0 -> bb1
    // PCG: bb1 -> bb4: Weaken RETURN from E to W
}

pub struct Holder<'a> {
    refs: Vec<&'a u32>,
}

impl Drop for Holder<'_> {
    fn drop(&mut self) {}
}

fn hold<'a>(h: &mut Holder<'a>, r: &'a u32) {
    h.refs.push(r);
}

// `hold` may store the borrow of `y` in `h` before it unwinds, so the unwind
// edge has the abstraction's edge into `h` as the return edge does.
fn borrow_stored_by_unwinding_call(y: u32) {
    let mut h = Holder { refs: Vec::new() };
    hold(&mut h, &y);
    // PCG: bb2 -> bb5: Add Edge call hold at bb2[11]: [_5 before bb2[11]:PostOperands↓'?11 before bb2[11]:PostMain, _7 before bb2[11]:PostOperands↓'?14 before bb2[11]:PostMain] -> [_5 before bb2[11]:PostOperands↓'?11 after bb2] under conditions bb0 -> bb1, bb1 -> bb2
}

// The borrows that end on an unwind edge expire on the edge, before the join at
// the cleanup block that other unwinding terminators share.

pub struct Pair {
    fst: String,
    snd: String,
}

fn use_pair(_x: &mut Pair) {}

fn consume(_s: String) {}

// `a` is lent to the reborrow moved into `use_pair` when that call unwinds, and
// `a.fst` is moved out when `consume` unwinds; both reach the cleanup block
// that drops `a`. The loan of `a` ends on the first edge.
fn reborrow_moved_into_unwinding_call(mut a: Pair) {
    let x = &mut a;
    use_pair(x);
    consume(a.fst);
    // PCG: bb0 -> bb5: Remove Edge borrow: x = &mut  a
    // PCG: bb0 -> bb5: Restore capability E to a
    // PCG: bb5[0] pre_operands: a.fst: W
    // PCG: bb5[0] pre_operands: a.snd: E
}

// `pair.fst` is lent to `len` when it unwinds, and written to (after the drop
// of its old value) on some of the other edges into the cleanup block that
// drops `pair`. The loan ends on the first edge, where `pair` also regains its
// capability, so the join does not weaken `pair` on the other edges.
fn read_borrow_into_unwinding_call(mut pair: Pair) -> usize {
    let n = pair.fst.len();
    pair.fst = String::new();
    n + pair.snd.len()
    // PCG: bb0 -> bb9: Remove Edge borrow: _3 before bb0[3]:PostOperands <before bb0[3]:PostMain> = & pair.fst
    // PCG: bb9[0] pre_operands: pair: E
    // ~PCG: bb1 -> bb9: unpack pair with capability R
}

fn noop() {}

// `v` itself is lent to `len` when it unwinds. The loan ends on that edge,
// where `v` also regains its capability, so `v` reaches the join with the edge
// where `noop` unwinds as it does there.
fn local_lent_to_unwinding_call(v: Vec<usize>) -> usize {
    let n = v.len();
    noop();
    n
    // PCG: bb0 -> bb4: Restore capability E to v
    // ~PCG: bb4[0] pre_operands: Restore capability E to v
}

pub struct Guard<'a>(&'a u32);

impl Drop for Guard<'_> {
    fn drop(&mut self) {}
}

pub struct Slot<'a> {
    guard: Guard<'a>,
}

// The edges of the assignment to `o.guard` exist only on the paths on which
// the first `noop` returns. They reach the cleanup block shared by all
// unwinding terminators along the unwind edges of the later ones, under the
// branch choice of the first `noop`'s normal edge, which excludes the path on
// which it unwinds.
fn assigned_before_later_unwinds<'a>(o: &mut Slot<'a>, y: &'a u32) {
    noop();
    o.guard = Guard(y);
    noop();
    noop();
    // PCG: bb7[0] pre_operands: _4 before bb2[0]:PostOperands↓'?12 -> (*o).guard↓'?10 before bb2[1]:PreOperands under conditions bb0 -> bb1, bb1 -> bb2
    // ~PCG: bb7[0] pre_operands: _4 before bb2[0]:PostOperands↓'?12 -> (*o).guard↓'?10 before bb2[1]:PreOperands
}

fn main() {}
