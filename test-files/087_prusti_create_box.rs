fn use_box(v: i32) -> Box<i32> {
    let x = Box::new(v);
    let y = *x;
    // x unpacks to its value *x and its own fields x.0 and x.1
    // PCG: bb1[3] pre_operands: *x: R
    // PCG: bb1[3] pre_operands: x.0: R
    // PCG: bb1[3] pre_operands: x.1: R
    assert!(v == y);
    let z = Box::new(y);
    assert!(v == *z);
    Box::new(*z)
}

fn main() {}
