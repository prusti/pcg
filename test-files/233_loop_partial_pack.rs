struct F {
    g: u32,
    h: u32,
}

struct X {
    f: F,
    i: u32,
}

// The expansion of `x.f` created to write `x.f.g` is packed back up as soon as
// both of its fields hold the same capability, but the expansion of `x` is not:
// the loop's invariant capabilities include `x.f`, and therefore `x` stays
// unpacked for the whole loop body.
//
// The packing of owned places is independent of `PCG_PACK_STRATEGY`, which
// governs borrow PCG expansion edges; this file runs in the default eager mode.
//
// The result is read after the loop to keep `x.f` live at the loop head.
// Without a use, `x.f` is not among the loop's invariant capabilities and `x`
// packs up completely.
fn partial_pack_in_loop(mut x: X, mut a: u32, b: u32, t: bool) -> u32 {
    // bb3[0] is `x.f.g = 1`, which unpacks `x.f`.
    // PCG: bb3[0] pre_main: unpack x.f with capability E
    // PCG: bb3[0] pre_main: x.f.g: W
    // PCG: bb3[0] pre_main: x.f.h: E
    // PCG: bb3[0] post_main: x.f.g: E
    // PCG: bb3[0] post_main: x.f.h: E

    // By the next statement `x.f` is packed again, while `x` is still expanded
    // into `x.f` and `x.i`.
    // PCG: bb3[1] pre_operands: x.f: E
    // PCG: bb3[1] pre_operands: x.i: E
    // ~PCG: bb3[1] pre_operands: x: E

    // bb3[3] is `a = b`; `x` remains expanded across it.
    // PCG: bb3[3] post_main: x.f: E
    // PCG: bb3[3] post_main: x.i: E
    // ~PCG: bb3[3] post_main: x: E
    while t {
        x.f.g = 1;
        a = b;
        x.f = F { g: 2, h: 3 };
    }
    x.f.g + x.i + a
}

fn main() {}
