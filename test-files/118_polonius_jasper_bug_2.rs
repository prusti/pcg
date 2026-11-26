// option PCG_POLONIUS: true
// PCG_EXPECTED_FAILURE: frame swap

struct S<'a, T> {
    a: &'a mut T
}

fn swap<'a, 'b: 'a, T>(x: &'b mut S<'a, T>, y: &'b mut S<'a, T>) -> &'a mut T {
    std::mem::swap(x.a, y.a);
    x.a
}

fn main(){}
