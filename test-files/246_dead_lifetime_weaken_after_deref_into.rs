// A place whose lifetime projections are dead is not weakened while an edge
// into it is still in the graph: removing `{x} -> {*x}` packs `*x` back into
// `x`, so `*x` is not weakened before it, and `x` is weakened once afterwards.
fn triple<'a, 'b, 'c>(x: &'a mut &'b mut &'c mut i32) {
    // PCG: bb0[1] pre_operands: Weaken x from E to W
    // ~PCG: bb0[1] pre_operands: Weaken *x from E to W
    ***x = 9;
}

struct Holder<'b> {
    r: &'b mut i32,
}

fn through_struct<'a, 'b>(h: &'a mut Holder<'b>) {
    // PCG: bb0[1] pre_operands: Weaken h from E to W
    // ~PCG: bb0[1] pre_operands: Weaken *h from E to W
    *h.r = 3;
}

fn main() {}
