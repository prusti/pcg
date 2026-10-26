//! Regression test: to obtain read capability for `f`, the PCG must not
//! collapse `f`, because `f.x` is blocked by a shared borrow. Instead, the
//! expansion of `f` is downgraded to read capability.

struct Foo {
    x: u32,
    y: bool,
}

fn client() {
    let mut f = Foo { x: 0, y: false };
    let x_ref = &f.x;
    f.y = false;
    // PCG: bb0[8] pre_operands: Weaken f.y from E to R
    // PCG: bb0[8] pre_operands: Restore capability R to f
    // PCG: bb0[8] post_operands: f: R
    // PCG: bb0[8] post_operands: f.x: R
    // PCG: bb0[8] post_operands: f.y: R
    // ~PCG: bb0[8] pre_operands: Collapse(RepackCollapse { to: _1, capability: R, guide: None, _marker: PhantomData<&()> })
    let f_ref = &f;
    let j = *x_ref;
}

/// The same situation for a place reached through a mutable reference. Here
/// the expansion of `*p` lives in the borrow PCG rather than the owned PCG,
/// and therefore a different mechanism keeps it in place: the expansion edge
/// is not a leaf while `(*p).x` is blocked, and re-expanding `*p` for read
/// downgrades `(*p).y`.
fn client_reborrow(p: &mut Foo) {
    let x_ref = &p.x;
    p.y = false;
    // PCG: bb0[5] post_operands: {*p} -> {(*p).x, (*p).y}
    // PCG: bb0[5] post_operands: *p: R
    // PCG: bb0[5] post_operands: (*p).x: R
    // PCG: bb0[5] post_operands: (*p).y: R
    let f_ref = &*p;
    let j = *x_ref;
}

/// Packing the read of `f.x` must not unfreeze `f` while `f_ref` is live.
fn read_while_shared(mut f: Foo) -> u32 {
    let f_ref = &f;
    let k = f.x;
    let j = f_ref.x;
    f.x = 3;
    // PCG: bb0[1] post_operands: Freeze f
    // PCG: bb0[5] pre_operands: Collapse(RepackCollapse { to: _1, capability: R, guide: None, _marker: PhantomData<&()> })
    // PCG: bb0[5] post_operands: f: R
    // ~PCG: bb0[5] pre_operands: Unfreeze f
    // PCG: bb0[9] pre_operands: Unfreeze f
    k + j
}

fn main() {}
