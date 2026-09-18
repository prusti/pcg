fn remote_shared(x: &i32) {
    // PCG_LIFETIME_DISPLAY: x 0 'x
    // PCG: bb1[0] pre_operands: Remote(_1)↓'x -> x↓'x
    // ~PCG: bb1[0] pre_operands: Loop(bb1): Remote(_1)↓'x -> x↓'x
    // ~PCG: bb1[0] pre_operands: Loop(bb1): x -> x↓'x
    // PCG: bb1[0] pre_operands: x: R
    // PCG: bb2[0] pre_operands: x: R
    loop {
        std::hint::black_box(&x);
    }
}

fn remote_mutable(x: &mut i32) {
    // PCG_LIFETIME_DISPLAY: x 0 'x
    // PCG: bb1[0] pre_operands: Remote(_1)↓'x -> x↓'x
    // ~PCG: bb1[0] pre_operands: Loop(bb1): Remote(_1)↓'x -> x↓'x
    // ~PCG: bb1[0] pre_operands: Loop(bb1): x -> x↓'x
    // PCG: bb1[0] pre_operands: x: R
    // PCG: bb2[0] pre_operands: x: R
    loop {
        std::hint::black_box(&x);
    }
}

fn local_root() {
    let mut value = 0;
    let r = &mut value;
    // PCG_LIFETIME_DISPLAY: r 0 'r
    // PCG: bb1[0] pre_operands: borrow: r = &mut  value
    // ~PCG: bb1[0] pre_operands: Loop(bb1): value -> r↓'r
    // PCG: bb1[0] pre_operands: r: R
    // PCG: bb2[0] pre_operands: r: R
    loop {
        std::hint::black_box(&r);
    }
}

fn reassigned_remote(mut x: &i32) {
    // PCG_LIFETIME_DISPLAY: x 0 'x
    // PCG: bb1[0] pre_operands: Loop(bb1): Remote(_1)↓'x -> x↓'x
    // ~PCG: bb1[0] pre_operands: Loop(bb1): x -> x↓'x
    loop {
        x = std::hint::black_box(x);
    }
}

fn reassigned_local() {
    let mut value = 0;
    let mut r = &mut value;
    // PCG_LIFETIME_DISPLAY: r 0 'r
    // PCG: bb1[0] pre_operands: Loop(bb1): value -> r↓'r
    loop {
        r = std::hint::black_box(r);
    }
}

fn mixed_blockers(mut moving: &i32, stable: &i32) {
    // PCG_LIFETIME_DISPLAY: moving 0 'moving
    // PCG_LIFETIME_DISPLAY: stable 0 'stable
    // PCG: bb1[0] pre_operands: Loop(bb1): Remote(_1)↓'moving -> moving↓'moving
    // PCG: bb1[0] pre_operands: Remote(_2)↓'stable -> stable↓'stable
    // ~PCG: bb1[0] pre_operands: Loop(bb1): Remote(_2)↓'stable -> stable↓'stable
    // PCG: bb1[0] pre_operands: moving: E
    // PCG: bb1[0] pre_operands: stable: R
    loop {
        moving = std::hint::black_box(moving);
        std::hint::black_box(stable);
    }
}

fn main() {}
