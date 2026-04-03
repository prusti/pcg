trait Foo<'a> {
    fn get<'b, T: FromMutref<'b>>(&'b mut self) -> T;
}

struct A<'a> {
    f: &'a mut i32,
}

impl<'a> Foo<'a> for A<'a> {
    fn get<'b, T: FromMutref<'b>>(&'b mut self) -> T {
        T::from_mutref(&mut self.f)
    }
}

trait FromMutref<'a> {
    fn from_mutref(x: &'a mut i32) -> Self;
}

impl<'a> FromMutref<'a> for &'a mut i32 {
    fn from_mutref(x: &'a mut i32) -> Self { x }
}

fn main() {
    let mut i = 42;
    let mut a = A {
        f: &mut i,
    };
    let b = a.get::<&mut i32>();
    // PCG: bb0[15] post_main: call Foo::get at bb0[15]: [_6 before bb0[15]:PostOperands↓'?24 before bb0[15]:PostMain, _6 before bb0[15]:PostOperands↓'?25 before bb0[15]:PostMain] -> [b↓'?23, _6 before bb0[15]:PostOperands↓'?25 after bb0]
    *b = 1;
    println!("{i}");
}