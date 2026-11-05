// Borrows inside `x` flow into the returned `impl Debug`, whose hidden type is
// `T`. The PCG does not look at hidden types, so it cannot tell that
// `RegionsIn(T)` outlives `RegionsIn(impl Debug)` and the edge is missing.
// This test documents that incompleteness.
fn f<T: std::fmt::Debug>(x: T) -> impl std::fmt::Debug {
    // ~PCG: bb0[0] post_main: Add Edge x before bb0[0]:PostOperands↓RegionsIn(T) -> RETURN↓RegionsIn(impl std::fmt::Debug)
    x
}

fn main() {}
