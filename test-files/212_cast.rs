// PCG_EXPECTED_FAILURE: frame main
// PCG_EXPECTED_FAILURE: label main
fn foo<T: ?Sized>(x: &T) -> &T {
    x
}

fn main() {
    let x: &[i32] = &[0, 1, 2];
    let y = foo::<[i32]>(x);
    println!("{y:?}")
}