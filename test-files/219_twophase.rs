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

pub struct Header<'a> {
    pub name: &'a str,
}

pub struct Request<'h, 'b> {
    pub method: Option<&'b str>,
    pub headers: &'h mut [Header<'b>],
}

impl<'h, 'b> Request<'h, 'b> {
    fn parse_uninit(
        &mut self,
        buf: &'b [u8],
        headers: &'h mut [std::mem::MaybeUninit<Header<'b>>],
    ) -> Result<usize, ()> {
        let _ = (buf, headers);
        Err(())
    }

    // The raw pointer `headers` keeps the loan of `(*self).headers` taken by
    // `mem::take` in the PCG, although its loan is dead: activating the
    // two-phase borrow of `*self` detaches the read copy `(*self).method`
    // that cannot be packed.
    pub fn parse(&mut self, buf: &'b [u8]) -> Result<usize, ()> {
        // PCG: bb1[26] pre_operands: Label place (*self).method (Detach)
        // PCG: bb1[26] pre_operands: Activate two-phase borrow borrow: _11 = &mut  *self
        let headers = std::mem::take(&mut self.headers);
        unsafe {
            let headers: *mut [Header<'_>] = headers;
            let headers = headers as *mut [std::mem::MaybeUninit<Header<'_>>];
            match self.parse_uninit(buf, &mut *headers) {
                Ok(idx) => Ok(idx),
                other => {
                    self.headers = &mut *(headers as *mut [Header<'_>]);
                    other
                }
            }
        }
    }
}

fn main() {}
