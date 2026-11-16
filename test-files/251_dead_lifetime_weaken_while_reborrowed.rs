// `_5 = &mut i` is dead after `_4 = &mut (*_5)`, but is weakened only once the
// reborrow held by `o` ends and `(*_5)` is packed back into it.
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
