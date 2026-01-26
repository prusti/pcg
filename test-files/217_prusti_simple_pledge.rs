fn ident<'a>(x: &'a mut i32) -> &'a mut i32 {
    x
}

fn main() {
    let mut x = 5;
    let y = ident(&mut x);
    *y = 1;
    assert!(x == 1);
}
