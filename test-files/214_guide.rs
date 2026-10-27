fn test() {
    let mut x = [13, 37, 72];
    let y: &mut [i32] = &mut x;
    y[1] = 3;
    // PCG: bb1[1] pre_operands: Remove Edge {*y} -> {(*y)[_5]} (guide=Index(_5)) returning E to *y
}

// `d` is read-unpacked at two indices while frozen: each collapse packs its
// own index at R, and `d` gets its E back only from its unfreeze.
fn read_at_two_indices(i: usize, j: usize) -> u32 {
    // PCG: bb2[8] pre_operands: Unfreeze d
    let mut d = [0u32; 4];
    let a = &d[i];
    let b = &d[j];
    let s = *a + *b;
    d[0] = s;
    d[0]
}
