/// Annotations are checked against the innermost body containing them: those
/// written inside the closure describe the closure body, and those written
/// outside it describe `outer`. The negative annotations pin that down — each
/// asserts that the *other* body's state is not checked against this one.
fn outer(v: &mut Vec<i32>) {
    let x = &mut v[0];
    // PCG: bb0[0] post_main: x: W
    // ~PCG: bb0[0] post_main: z: W
    let f = |y: &mut i32| {
        let z = &mut *y;
        // PCG: bb0[0] post_main: z: W
        // ~PCG: bb0[0] post_main: x: W
        *z += 1;
    };
    f(x);
}
