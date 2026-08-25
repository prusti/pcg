// option PCG_PACK_STRATEGY: lazy
struct Point {
    x: u32,
    y: u32,
}

fn read_fields_then_overwrite(p: &mut Point) {
    let _x = p.x;
    let _y = p.y;
    // Under the eager strategy the expansion of `*p` is packed up as soon as
    // both fields hold the same capability, i.e. here. Under the lazy strategy
    // it survives until a capability to `*p` is required.
    // ~PCG: bb0[5] pre_operands: Remove Edge {*p} -> {(*p).x, (*p).y}
    // PCG: bb0[5] post_main: {*p} -> {(*p).x, (*p).y}
    // PCG: bb0[5] post_main: (*p).x: R
    // PCG: bb0[5] post_main: (*p).y: R

    // Overwriting `*p` requires a capability that `*p` cannot hold while it is
    // expanded, so the expansion is packed just in time.
    // PCG: bb0[8] pre_main: Remove Edge {*p} -> {(*p).x, (*p).y}
    // PCG: bb0[8] pre_main: Restore *p to E
    *p = Point { x: 1, y: 2 };
}

fn main() {}
