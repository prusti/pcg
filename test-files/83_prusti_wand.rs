struct T {
    val: i32
}

fn identity_use2() {
    let mut t = T { val: 5 };
    assert!(t.val == 5);
    // PCG: bb0[6] pre_main: Repacks Start: Expand(_1, _1.0, R)
    let y = &mut t;
}

fn main() {}
