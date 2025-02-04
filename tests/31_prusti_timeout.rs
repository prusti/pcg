#[derive(Eq, PartialEq)]
pub struct T {
    val: u32,
}

fn cmp(_l: &T, _r: &T) -> bool {
    unimplemented!();
}

pub struct P {
    f: T,
}

pub fn test1(s: &mut P, now: T) {
    if cmp(&now, &s.f) {
        s.f = now;
    }
}

pub struct Pair<T> {
    pub first: T,
    pub second: T,
}

pub fn foo<T>(_a: T, _b: T) -> T {
    unimplemented!();
}

pub fn test2<T: Copy>(x: &Pair<T>) -> T {
    foo(x.first, x.second)
}

use std::ops::Add;
impl<'a, T> Add<&'a Pair<T>> for Pair<T> {
    type Output = Pair<T>;

    fn add(self, other: &'a Pair<T>) -> Pair<T> {
        unimplemented!();
    }
}

pub fn bar<T>(_a: Pair<T>, _b: &Pair<T>) -> Pair<T> {
    unimplemented!();
}

pub fn test3<T>(s: &Pair<T>, i: Pair<T>) -> Pair<T> {
    i + s
}

pub fn test4<T>(s: &Pair<T>, i: Pair<T>) -> Pair<T> {
    bar(i, s)
}

fn main() {}
