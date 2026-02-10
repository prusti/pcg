struct Tmp {}

impl Tmp {
    fn read(&self) -> Self {
        Tmp {}
    }

    fn write (&mut self, x: Self) {

    }
}

fn foo() {
    let mut x = Tmp {};
    x.write(x.read());
}
