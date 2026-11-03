// Edges from the arguments of a call into its result. Only regions that may
// flow into the result according to both the callee's signature and the
// borrow checker get an edge.

// The result of `take` cannot hold the local `&mut v` borrow, so it does not
// block `v`, which must be available again for the implicit `drop(v)`.
fn take<T>(v: &mut Vec<T>) -> T {
    unimplemented!()
}

// The caller chooses `T`, so a value of type `T` cannot hold a borrow created
// in the body.
fn generic<T>(mut v: Vec<T>) -> T {
    // PCG: bb0[4] post_main: Add Edge call take at bb0[4]: [_2 before bb0[4]:PostOperands↓RegionsIn(T) before bb0[4]:PostMain] -> [RETURN↓RegionsIn(T), _2 before bb0[4]:PostOperands↓RegionsIn(T) after bb0]
    // PCG: bb1[2] pre_operands: v: E
    take(&mut v)
}

// The result has type `&'static i32`, so it cannot hold the borrow even though
// `take` returns its type parameter `T`.
fn static_ref(mut v: Vec<&'static i32>) -> &'static i32 {
    // PCG: bb0[5] post_main: Add Edge call take at bb0[5]: [_3 before bb0[5]:PostOperands↓'?10 before bb0[5]:PostMain] -> [_2↓'?8, _3 before bb0[5]:PostOperands↓'?10 after bb0]
    // PCG: bb1[2] pre_operands: v: E
    take(&mut v)
}

fn id<T>(x: T) -> T {
    x
}

// Both references map to `RegionsIn(T)` in the signature of `id`, but the
// borrows under `'a` and `'b` do not flow into each other.
fn id_pair<'a, 'b>(x: (&'a mut i32, &'b mut i32)) -> (&'a mut i32, &'b mut i32) {
    // PCG: bb0[2] post_main: Add Edge call id at bb0[2]: _2 before bb0[2]:PostOperands↓'?10 before bb0[2]:PostMain -> RETURN↓'?6
    // PCG: bb0[2] post_main: Add Edge call id at bb0[2]: _2 before bb0[2]:PostOperands↓'?11 before bb0[2]:PostMain -> RETURN↓'?7
    // ~PCG: bb0[2] post_main: Add Edge call id at bb0[2]: _2 before bb0[2]:PostOperands↓'?10 before bb0[2]:PostMain -> RETURN↓'?7
    // ~PCG: bb0[2] post_main: Add Edge call id at bb0[2]: _2 before bb0[2]:PostOperands↓'?11 before bb0[2]:PostMain -> RETURN↓'?6
    id(x)
}

fn main() {}
