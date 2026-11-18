//! Regression test: to obtain read capability for `f`, the PCG must not
//! collapse `f`, because `f.x` is blocked by a shared borrow. Instead, the
//! unpacked `f` is frozen, which makes its fields read copies. The read
//! unpacking of a place that must become exclusive is packed, detaching the
//! borrowed referents of shared references in it.

struct Foo {
    x: u32,
    y: bool,
}

fn client() {
    let mut f = Foo { x: 0, y: false };
    let x_ref = &f.x;
    // Writing `f.y` moves the freeze of `f` to the borrowed `f.x`.
    // PCG: bb0[4] pre_operands: Freeze f
    // PCG: bb0[6] pre_main: Refreeze f to f.x
    f.y = false;
    // PCG: bb0[8] pre_operands: Freeze f
    // ~PCG: bb0[8] pre_operands: Weaken f.y from E to R
    // PCG: bb0[8] post_operands: f: R
    // PCG: bb0[8] post_operands: f.x: R
    // PCG: bb0[8] post_operands: f.y: R
    // ~PCG: bb0[8] pre_operands: Collapse(RepackCollapse { to: _1, capability: R, guide: None, _marker: PhantomData<&()> })
    let f_ref = &f;
    let j = *x_ref;
}

/// The same situation for a place reached through a mutable reference. Here
/// the expansion of `*p` lives in the borrow PCG rather than the owned PCG,
/// and therefore a different mechanism keeps it in place: the expansion edge
/// is not a leaf while `(*p).x` is blocked, and `*p` is frozen in place.
fn client_reborrow(p: &mut Foo) {
    let x_ref = &p.x;
    p.y = false;
    // PCG: bb0[3] pre_main: Refreeze p to (*p).x
    // PCG: bb0[5] pre_operands: Freeze *p
    // PCG: bb0[5] post_operands: {*p} -> {(*p).x, (*p).y}
    // PCG: bb0[5] post_operands: *p: R
    // PCG: bb0[5] post_operands: (*p).x: R
    // PCG: bb0[5] post_operands: (*p).y: R
    let f_ref = &*p;
    let j = *x_ref;
}

/// Packing the read of `f.x` must not unfreeze `f` while `f_ref` is live.
fn read_while_shared(mut f: Foo) -> u32 {
    let f_ref = &f;
    let k = f.x;
    let j = f_ref.x;
    f.x = 3;
    // PCG: bb0[1] post_operands: Freeze f
    // PCG: bb0[5] pre_operands: Collapse(RepackCollapse { to: _1, capability: R, guide: None, _marker: PhantomData<&()> })
    // PCG: bb0[5] post_operands: f: R
    // ~PCG: bb0[5] pre_operands: Unfreeze f
    // PCG: bb0[8] pre_operands: Unfreeze f
    k + j
}

struct Raw {
    p: *mut u32,
    q: u32,
}

/// The dereference of the raw pointer `s.p` is part of the read unpacking of
/// `s`, not a borrow of `s.p`: writing `s.q` unfreezes all of `s`, and `s.p`
/// stays unpacked with `e`.
unsafe fn raw_field_read(mut s: Raw) -> u32 {
    let a = unsafe { *s.p };
    s.q = a;
    // PCG: bb0[1] pre_operands: Freeze s
    // PCG: bb0[5] pre_main: Unfreeze s
    // PCG: bb0[5] post_main: s.p: e
    // ~PCG: bb0[5] pre_main: Refreeze s to s.p
    let b = s.p;
    unsafe { *b + s.q }
}

struct Pair {
    m: u32,
    n: u32,
}

/// The frozen `p` is unpacked by the dereference of the raw pointer, and a
/// part of the unpacking is borrowed: `p` is not a leaf that can be unfrozen.
unsafe fn raw_part_borrowed(p: *mut Pair) -> u32 {
    unsafe {
        let r = &(*p).m;
        let n = (*p).n;
        // PCG: bb0[2] pre_operands: (*p).m: R
        // ~PCG: bb0[2] pre_operands: Unfreeze p
        n + *r
    }
}

/// Reading through the raw pointer `p` freezes `p`, whose unpacking stays
/// after the read, while the other path unpacks `p` exclusively. The join
/// ends the freeze, so that `p` keeps a capability.
unsafe fn raw_read_or_write(p: *mut u32, b: bool) -> *mut u32 {
    unsafe {
        if b {
            let _x = *p;
        } else {
            *p = 1;
        }
        // PCG: bb3[0] post_main: p: e
        // PCG: bb3[0] post_main: *p: E
        p
    }
}

struct Buf {
    ptr: *mut u8,
    len: usize,
}

impl Buf {
    /// The same join, for a raw pointer reached through a mutable reference.
    unsafe fn read_or_write(&mut self, b: bool) -> usize {
        unsafe {
            if b {
                let _x = *self.ptr;
            } else {
                *self.ptr = 0;
            }
            // PCG: bb3[0] post_main: self: e
            // PCG: bb3[0] post_main: (*self).ptr: e
            // PCG: bb3[0] post_main: *(*self).ptr: E
            self.len
        }
    }
}

/// Reading `(*s).q` does not unpack `s` again: the existing exclusive
/// unpacking of `s` already holds `(*s).q`.
unsafe fn raw_read_after_write(s: *mut Raw) -> u32 {
    unsafe {
        *(*s).p = 1;
        // PCG: bb0[1] post_main: s: e
        // PCG: bb0[1] post_main: (*s).q: E
        // ~PCG: bb0[1] post_main: *s: R
        (*s).q
    }
}

/// The join keeps the unpacking of `p` from the first path, but `*p` holds
/// nothing after it: reading `*p` unpacks `p` again.
unsafe fn raw_read_after_conditional_write(p: *mut u32, b: bool) -> u32 {
    unsafe {
        if b {
            *p = 1;
        }
        // PCG: bb3[2] pre_operands: *p: R
        *p
    }
}

struct Inner {
    f: u32,
    g: u32,
}

struct Outer {
    s: Inner,
    v: Vec<u32>,
}

/// In the loop, `t.s.f` stays frozen while the loop's abstraction edge
/// borrows it, until `r` is overwritten.
fn loop_borrowed_field(mut t: Outer, n: usize) -> Outer {
    let mut i = 0;
    let mut r = &t.s.f;
    // PCG: bb1[0] pre_operands: t.s.f: R
    // ~PCG: bb1[0] pre_operands: Unfreeze t.s.f
    // PCG: bb4[0] pre_operands: Unfreeze t.s.f
    while i < n {
        if i == 3 {
            r = &t.s.g;
        }
        t.v.push(*r);
        i += 1;
    }
    t.s.f = 1;
    t
}

struct Mid {
    a: Foo,
    b: u32,
}

struct Top {
    y: Mid,
    z: u32,
}

/// When `x` ends, `(*p).y.a` is packed while `r` still borrows `(*p).y`: it
/// comes back as a read copy of the frozen `(*p).y`.
fn pack_under_frozen(p: &mut Top) {
    let x = &p.y.a.x;
    p.y.b = 3;
    let r = &p.y;
    let _ = *x;
    // PCG: bb0[5] pre_operands: Freeze (*p).y
    // PCG: bb0[8] pre_operands: Remove Edge {(*p).y.a} -> {(*p).y.a.x, (*p).y.a.y} returning R to (*p).y.a
    // ~PCG: bb0[8] pre_operands: Remove Edge {(*p).y.a} -> {(*p).y.a.x, (*p).y.a.y} returning E to (*p).y.a
    let _ = r.b;
    p.y.b = 4;
}

// A borrow of the referent of a shared reference does not depend on the place
// holding the reference: when that place must become exclusive, the referent
// is labelled and detached, and the read unpacking is packed.
struct Dfa {
    classes: Vec<u8>,
    inner: &'static Dfa,
}

struct Lazy<'a> {
    dfa: &'a Dfa,
    cache: Vec<u8>,
}

impl<'a> Lazy<'a> {
    fn set(&mut self, x: u8) {
        self.cache.push(x);
    }

    /// The loop head holds `*self` with E while the iterator still borrows
    /// `classes`: entering the loop detaches the referent of `self.dfa`.
    fn loop_entry(&mut self) {
        // PCG: bb4[0] pre_operands: borrow: _6 before bb0[6]:PostOperands <before bb0[6]:PostMain> = & (*(*self).dfa).classes loop bb4
        // ~PCG: bb4[0] pre_operands: {*self} -> {(*self).dfa, (*self).cache}
        // PCG: bb4[0] pre_operands: Remove Edge {self} -> {*self} returning E to self
        // PCG: bb7[0] pre_operands: Remove Edge borrow: _6 before bb0[6]:PostOperands <before bb0[6]:PostMain> = & (*(*self).dfa).classes loop bb4 under conditions bb6 -> bb7
        for c in self.dfa.classes.iter() {
            self.set(*c);
        }
    }

    /// The two-phase borrow of `*self` is activated while `it` borrows
    /// `classes`.
    fn activation(&mut self) {
        // PCG: bb2[6] pre_operands: Refreeze self to *self
        // PCG: bb2[6] pre_operands: Label place *(*self).dfa (DetachSharedReferent)
        // PCG: bb2[6] pre_operands: Remove Edge {(*self).dfa} -> {*(*self).dfa before bb2[6]:PreOperands}
        // PCG: bb2[6] pre_operands: Remove Edge {*self} -> {(*self).dfa, (*self).cache}
        // PCG: bb2[6] pre_operands: Activate two-phase borrow borrow: _7 = &mut  *self
        // ~PCG: bb2[6] pre_operands: Weaken *(*self).dfa from R to None
        // PCG: bb4[0] pre_operands: Remove Edge borrow: _5 before bb0[5]:PostOperands <before bb0[5]:PostMain> = & (*(*self).dfa).classes before bb2[6]:PreOperands
        let mut it = self.dfa.classes.iter();
        self.set(0);
        it.next();
    }

    /// `*self` is reborrowed mutably while `c` borrows `classes`.
    fn reborrow(&mut self) -> u8 {
        // PCG: bb1[4] pre_operands: Label place *(*self).dfa (DetachSharedReferent)
        // PCG: bb1[4] pre_operands: Remove Edge {(*self).dfa} -> {*(*self).dfa before bb1[4]:PreOperands}
        // PCG: bb1[4] pre_operands: Remove Edge {*self} -> {(*self).dfa, (*self).cache}
        // PCG: bb1[4] pre_operands: Unfreeze self
        let c = &self.dfa.classes[0];
        let r = &mut *self;
        r.cache.push(1);
        *c
    }

    /// Only the outermost borrowed referent is detached.
    fn nested(&mut self) -> u8 {
        // PCG: bb1[4] pre_operands: Label place *(*self).dfa (DetachSharedReferent)
        // ~PCG: bb1[4] pre_operands: Label place *(*(*self).dfa).inner (DetachSharedReferent)
        // PCG: bb1[4] pre_operands: Unfreeze self
        let c = &self.dfa.inner.classes[0];
        let r = &mut *self;
        r.cache.push(1);
        *c
    }
}

/// The upgraded place is the frozen reference itself: packing its read
/// unpacking ends its freeze, once.
fn frozen_root<'a>(mut x: &mut Lazy<'a>) -> u8 {
    // PCG: bb1[4] pre_operands: Label place *(*x).dfa (DetachSharedReferent)
    // PCG: bb1[4] pre_operands: Remove Edge {x} -> {*x}
    // PCG: bb1[4] pre_operands: Unfreeze x
    let c = &x.dfa.classes[0];
    let r = &mut x;
    r.cache.push(1);
    *c
}

fn frozen_root_in_loop<'a>(mut y: &mut Lazy<'a>) {
    // PCG: bb4[0] pre_operands: borrow: _6 before bb0[6]:PostOperands <before bb0[6]:PostMain> = & (*(*y).dfa).classes loop bb4
    // PCG: bb4[0] pre_operands: y: E
    // ~PCG: bb4[0] pre_operands: {y} -> {*y}
    for c in y.dfa.classes.iter() {
        let r = &mut y;
        r.cache.push(*c);
    }
}

/// The two-phase borrow of the owned `l` is activated while `it` borrows
/// `classes`: the referent is detached before the read unpacking of `l` is
/// packed.
fn owned_activation(mut l: Lazy<'_>) -> Lazy<'_> {
    // PCG: bb2[6] pre_operands: Label place *l.dfa (DetachSharedReferent)
    // PCG: bb2[6] pre_operands: Collapse(RepackCollapse { to: _1, capability: R, guide: None, _marker: PhantomData<&()> })
    // PCG: bb2[6] pre_operands: Activate two-phase borrow borrow: _7 = &mut  l
    let mut it = l.dfa.classes.iter();
    l.set(0);
    it.next();
    l
}

fn main() {}
