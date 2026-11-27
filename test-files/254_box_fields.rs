// A box `b` unpacks to its value `*b` and its own fields `b.0` (the pointer)
// and `b.1` (the allocator). Moving the value out leaves `b.0` and `b.1` at
// `E`; dropping or overwriting the box weakens them and packs `b`.

struct S {
    v: i32,
}

fn consume(_s: S) {}

fn move_out(b: Box<S>) {
    // PCG: bb0[1] post_main: *b: W
    // PCG: bb0[1] post_main: b.0: E
    // PCG: bb0[1] post_main: b.1: E
    // PCG: bb1[4] post_main: b: W
    let s = *b;
    consume(s);
}

fn reinit_after_move(mut b: Box<S>) {
    // ~PCG: bb0[5] pre_main: unpack b with capability W
    // PCG: bb0[5] post_main: *b: E
    // PCG: bb0[6] pre_operands: Collapse(RepackCollapse { to: _1, capability: E, guide: None, _marker: PhantomData<&()> })
    let s = *b;
    *b = S { v: 2 };
    consume(s);
    consume(*b);
}

fn reassign_after_move(mut b: Box<S>) {
    // PCG: bb1[1] pre_main: Collapse(RepackCollapse { to: _1, capability: W, guide: None, _marker: PhantomData<&()> })
    // PCG: bb1[1] post_main: b: W
    let s = *b;
    b = Box::new(s);
    consume(*b);
}

fn join_moved_and_kept(c: bool, b: Box<S>) {
    // PCG: bb3 -> bb4: unpack b with capability E
    // ~PCG: bb3 -> bb4: unpack b with capability W
    // PCG: bb4[0] post_main: *b: W
    // PCG: bb4[0] post_main: b.0: E
    // PCG: bb4[0] post_main: b.1: E
    if c {
        consume(*b);
    }
}

fn borrow_through(b: &mut Box<S>) -> &mut i32 {
    // PCG: bb0[2] post_main: {*b} -> {(*b).0, (*b).1, **b}
    // PCG: bb0[2] post_main: (*b).0: E
    // PCG: bb0[2] post_main: (*b).1: E
    &mut b.v
}

struct R<'a> {
    r: &'a mut i32,
}

fn take<'a>(_b: Box<R<'a>>) {}

// The pointer field `b.0` has no lifetime projections: the borrows of the box
// are those of its value, so packing `b` maps only the projection of `*b` to
// that of `b`.
fn collapse_lifetime_projections<'a>(mut b: Box<R<'a>>, x: &'a mut i32) {
    // PCG: bb0[3] post_main: *b before bb0[3]:PreOperands↓'?5 -> b↓'?5
    // ~PCG: bb0[3] post_main: b.0 before bb0[3]:PreOperands↓'?5 -> b↓'?5
    b.r = x;
    take(b);
}

fn loop_read(b: Box<S>, n: i32) -> i32 {
    // PCG: bb1[0] pre_operands: *b: R
    // PCG: bb1[0] pre_operands: b.0: R
    // PCG: bb1[0] pre_operands: b.1: R
    let mut i = 0;
    let mut acc = 0;
    while i < n {
        acc = b.v;
        i += 1;
    }
    acc
}

fn loop_write_value(mut b: Box<S>, n: i32) {
    // PCG: bb1[0] pre_operands: *b: E
    // PCG: bb1[0] pre_operands: b.0: E
    // PCG: bb1[0] pre_operands: b.1: E
    let mut i = 0;
    while i < n {
        *b = S { v: i };
        i += 1;
    }
}

fn loop_reassign(mut b: Box<S>, n: i32) {
    // PCG: bb2[0] pre_operands: *b: W
    // PCG: bb2[0] pre_operands: b.0: E
    // PCG: bb2[0] pre_operands: b.1: E
    consume(*b);
    let mut i = 0;
    while i < n {
        b = Box::new(S { v: i });
        i += 1;
    }
}

fn main() {}
