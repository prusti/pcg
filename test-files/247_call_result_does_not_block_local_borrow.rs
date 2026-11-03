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

fn main() {}
