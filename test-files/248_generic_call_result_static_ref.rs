// The result of `take` has type `&'static i32`, so it cannot hold the local
// `&mut v` borrow even though `take` returns its type parameter `T`. The
// result therefore does not block `v`, which must be available again for the
// implicit `drop(v)`.
fn take<T>(v: &mut Vec<T>) -> T {
    unimplemented!()
}

fn f(mut v: Vec<&'static i32>) -> &'static i32 {
    take(&mut v)
}

fn main() {}
