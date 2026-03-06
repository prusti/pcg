fn main() {}

struct S<'a> {
    iter: std::slice::Iter<'a, u8>,
    f: fn(),
}

impl<'a> S<'a> {
    fn go(&mut self) {
        for _ in &mut self.iter {
            (self.f)();
        }
    }
}
