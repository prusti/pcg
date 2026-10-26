// A reference whose lifetime projections are dead is weakened only once it is
// no longer dereferenced: `x` must not be weakened while `{x} -> {*x}` is still
// in the graph, but once after it has been removed.
fn write_inner<'a, 'b>(x: &'a mut &'b mut i32) {
    // PCG: bb0[1] pre_operands: Weaken x from E to W
    // ~PCG: bb0[1] pre_operands: Weaken x from e to W
    **x = 5;
}

fn main() {}
