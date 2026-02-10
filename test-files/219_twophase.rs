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
    // PCG: bb1[1] pre_operands: Weaken x from R to None
    // `x`'s capability should be removed when the two-phase borrow is activated
}
