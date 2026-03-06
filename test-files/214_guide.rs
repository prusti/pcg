fn test() {
    let mut x = [13, 37, 72];
    let y: &mut [i32] = &mut x;
    y[1] = 3;
    // PCG: bb1[1] pre_operands: Remove Edge {*y} -> {(*y)[_5]} (guide=Index(_5, ()))
}
