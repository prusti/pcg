// A reference whose lifetime projections are dead is not weakened while its
// target is reborrowed: `_5 = &mut i` is dead after `_4 = &mut (*_5)`, but
// `{_5} -> {(*_5)}` stays in the graph until the reborrow held by `o` ends,
// and ending it packs `(*_5)` back into `_5`.
struct O<'a, 'b> {
    x: &'b mut &'a mut u32,
}

fn f() {
    let mut n = 4;
    let mut i = &mut n;
    // ~PCG: bb0[11] pre_operands: Weaken _5 from e to W
    // PCG: bb0[14] pre_operands: Weaken _5 from E to W
    let o = O { x: &mut i };
}

fn main() {}
