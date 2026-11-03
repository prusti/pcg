// A region outlives `RegionsIn(T)` only if it outlives `'static`, since `T`
// may contain `'static`.

fn tuple_move_static<T>(x: (T, &'static u32)) -> (T, &'static u32) {
    // PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓'?3 -> y↓RegionsIn(T)
    let y = x;
    y
}

fn tuple_move<'a, T>(x: (T, &'a u32)) -> (T, &'a u32) {
    // ~PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓'?4 -> y↓RegionsIn(T)
    let y = x;
    y
}

fn main() {}
