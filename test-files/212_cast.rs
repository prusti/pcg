fn foo<T: ?Sized>(x: &T) -> &T {
    x
}

fn main() {
    let x: &[i32] = &[0, 1, 2];
    let y = foo::<[i32]>(x);
    println!("{y:?}")
}