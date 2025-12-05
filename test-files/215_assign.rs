fn user(x: [i32; 3]) {}

fn main() {
    let mut x = [13, 37, 72];
    let y: &mut [i32] = &mut x;
    // PCG: bb0[8] post_main: _3 before bb0[8]:PostOperands↓'?6 -> y↓'?5 with cast PointerCoercion(Unsize, Implicit)
    y[1] = 3;
    user(x);
}
