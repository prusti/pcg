struct T {
    val: i32
}

fn identity_use2() {
    let mut t = T { val: 5 };
    // PCG: bb0[6] pre_operands: unpack t with capability R
    assert!(t.val == 5);

    let y = &mut t;
}

fn main() {}
