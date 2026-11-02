// A value of an opaque type `T` cannot hold a borrow created in the body,
// since the caller chooses `T`. The result of `take` therefore does not block
// `v`, which must be available again for the implicit `drop(v)`.
fn take<T>(v: &mut Vec<T>) -> T {
    unimplemented!()
}

fn f<T>(mut v: Vec<T>) -> T {
    take(&mut v)
}

fn main() {}
