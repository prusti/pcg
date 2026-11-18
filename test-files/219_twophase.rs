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
    // PCG: bb2[0] pre_operands: Remove Edge borrow: _3 before bb1[1]:PostOperands <before bb1[1]:PostMain> = &mut  x returning E to x
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
    // PCG: bb1[0] pre_operands: Remove Edge borrow: _3 before bb0[5]:PostOperands <before bb0[5]:PostMain> = &mut  v returning E to v
    v
}

fn field_read_borrowed(v: &mut V) {
    v.set(v.n);
    // PCG: bb0[2] post_operands: Freeze *v
    // PCG: bb0[5] pre_operands: Activate two-phase borrow borrow: _3 = &mut  *v
    // PCG: bb1[0] pre_operands: Remove Edge borrow: _3 before bb0[5]:PostOperands <before bb0[5]:PostMain> = &mut  *v returning E to *v
}

fn under_mut_ref(w: &mut W) {
    w.v.set(w.k);
    // The reservation unpacks `*w` exclusively, so `(*w).k` keeps E.
    // PCG: bb0[2] post_operands: Freeze (*w).v
    // PCG: bb0[2] post_operands: (*w).k: E
    // PCG: bb0[5] pre_operands: Activate two-phase borrow borrow: _3 = &mut  (*w).v
    // PCG: bb1[0] pre_operands: Remove Edge borrow: _3 before bb0[5]:PostOperands <before bb0[5]:PostMain> = &mut  (*w).v returning E to (*w).v
}

impl W {
    fn set_k(&mut self, x: usize) {
        self.k = x;
    }

    fn total(&self) -> usize {
        self.k
    }
}

fn under_shared_borrow(mut w: W) -> W {
    let r = &w;
    w.v.set(r.k);
    // The reservation is made under the freeze of `w`, which moves to `w.v`
    // once `r` is gone.
    // PCG: bb0[1] post_operands: Freeze w
    // PCG: bb0[8] pre_operands: Refreeze w to w.v
    // PCG: bb0[8] pre_operands: Activate two-phase borrow borrow: _4 = &mut  w.v
    // ~PCG: bb0[8] pre_operands: Weaken w from R to None
    // ~PCG: bb1[0] pre_operands: Unfreeze w.k
    w
}

fn ancestor_read(mut w: W) -> W {
    w.v.set(w.total());
    // Reading `w` during the reservation freezes all of it; the freeze moves
    // back to `w.v` at the activation.
    // PCG: bb0[2] post_operands: Freeze w.v
    // PCG: bb0[5] pre_operands: Freeze w
    // PCG: bb1[1] pre_operands: Refreeze w to w.v
    // PCG: bb1[1] pre_operands: Activate two-phase borrow borrow: _3 = &mut  w.v
    w
}

fn under_borrowed_part(mut w: W) -> W {
    let r = &w.v.n;
    w.k = 1;
    w.set_k(*r);
    // `w.v.n` is borrowed at the reservation of `w`, so the reservation reads
    // `w` instead of packing it exclusively.
    // PCG: bb0[6] pre_operands: Freeze w
    // PCG: bb0[6] post_main: w.v.n: R
    w
}

struct P {
    p: *mut V,
}

// The reserved place lies behind a shared reference, so the reservation reads
// it.
unsafe fn behind_shared_ref(s: &P, x: usize) {
    unsafe { (*s.p).set(x) }
}

struct Node<T> {
    entry: T,
    next: u32,
}

impl<T> Node<T> {
    fn entry_mut(&mut self) -> &mut T {
        &mut self.entry
    }
}

// The borrow checker does not track borrows of places behind a raw pointer: it
// never activates the two-phase borrow of `*node` and does not consider `*node`
// borrowed, so the freeze of the reservation ends at the next statement, as a
// mutable borrow of `*node` would.
unsafe fn behind_raw_ptr<'a, T>(node: *mut Node<T>) -> &'a mut T {
    unsafe {
        let entry = (*node).entry_mut();
        let _next = (*node).next;
        // PCG: bb0[4] post_operands: Freeze *node
        // PCG: bb0[5] pre_operands: Unfreeze *node
        entry
    }
}

struct Bytes {
    pos: usize,
}

impl Bytes {
    fn advance(&mut self, n: usize) {
        self.pos += n;
    }
}

impl AsRef<usize> for Bytes {
    fn as_ref(&self) -> &usize {
        &self.pos
    }
}

fn reservation_reads_reference(bytes: &mut Bytes) {
    // `bytes.as_ref()` borrows the reference `bytes` itself (through the
    // `AsRef` impl for `&mut Bytes`) while `*bytes` is reserved: `bytes`,
    // whose referent is unpacked (e), is frozen.
    // PCG: bb0[2] post_operands: Freeze *bytes
    // PCG: bb0[6] post_operands: Freeze bytes
    // PCG: bb1[2] pre_operands: Refreeze bytes to *bytes
    // PCG: bb1[2] pre_operands: Activate two-phase borrow borrow: _3 = &mut  *bytes
    bytes.advance(*bytes.as_ref());
}

fn main() {}
