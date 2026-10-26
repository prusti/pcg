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
    // The reservation freezes `x`; the activation lends the frozen capability.
    // PCG: bb0[5] post_operands: Freeze x
    // PCG: bb1[1] pre_operands: Activate two-phase borrow borrow: _3 = &mut  x
    // PCG: bb2[0] pre_operands: Restore capability E to x
    // ~PCG: bb1[1] pre_operands: Weaken x from R to None
}

struct V {
    n: usize,
    m: usize,
}

impl V {
    fn set(&mut self, x: usize) {
        self.m = x;
    }
}

struct W {
    v: V,
    k: usize,
}

fn field_read(mut v: V) -> V {
    v.set(v.n);
    // The read unpacks the frozen `v` at R, and is packed before activation.
    // PCG: bb0[2] post_operands: Freeze v
    // PCG: bb0[4] pre_operands: unpack v with capability R
    // PCG: bb0[5] pre_operands: Collapse(RepackCollapse { to: _1, capability: R, guide: None, _marker: PhantomData<&()> })
    // PCG: bb0[5] pre_operands: Activate two-phase borrow borrow: _3 = &mut  v
    // PCG: bb1[0] pre_operands: Restore capability E to v
    v
}

fn field_read_borrowed(v: &mut V) {
    v.set(v.n);
    // PCG: bb0[2] post_operands: Freeze *v
    // PCG: bb0[5] pre_operands: Activate two-phase borrow borrow: _3 = &mut  *v
    // PCG: bb1[0] pre_operands: Restore *v to E
}

fn under_mut_ref(w: &mut W) {
    w.v.set(w.k);
    // The reservation unpacks `*w` exclusively, so `(*w).k` keeps E.
    // PCG: bb0[2] post_operands: Freeze (*w).v
    // PCG: bb0[2] post_operands: (*w).k: E
    // PCG: bb0[5] pre_operands: Activate two-phase borrow borrow: _3 = &mut  (*w).v
    // PCG: bb1[0] pre_operands: Restore (*w).v to E
}

fn main() {}
