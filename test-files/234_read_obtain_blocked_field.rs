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

fn main() {}
