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
        // PCG: bb3 -> bb4: Label place *(*self).dfa (Detach)
        // PCG: bb3 -> bb4: Remove Edge {(*self).dfa} -> {*(*self).dfa loop bb4}
        // PCG: bb3 -> bb4: Remove Edge {*self} -> {(*self).dfa, (*self).cache}
        // PCG: bb3 -> bb4: Unfreeze self
        // ~PCG: bb3 -> bb4: Weaken (*(*self).dfa).classes from R to None
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
        // PCG: bb2[6] pre_operands: Label place *(*self).dfa (Detach)
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
        // PCG: bb1[4] pre_operands: Label place *(*self).dfa (Detach)
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
        // PCG: bb1[4] pre_operands: Label place *(*self).dfa (Detach)
        // ~PCG: bb1[4] pre_operands: Label place *(*(*self).dfa).inner (Detach)
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
    // PCG: bb1[4] pre_operands: Label place *(*x).dfa (Detach)
    // PCG: bb1[4] pre_operands: Remove Edge {x} -> {*x}
    // PCG: bb1[4] pre_operands: Unfreeze x
    let c = &x.dfa.classes[0];
    let r = &mut x;
    r.cache.push(1);
    *c
}

fn frozen_root_in_loop<'a>(mut y: &mut Lazy<'a>) {
    // PCG: bb3 -> bb4: Label place *(*y).dfa (Detach)
    // PCG: bb3 -> bb4: Remove Edge {y} -> {*y}
    // PCG: bb3 -> bb4: Unfreeze y
    for c in y.dfa.classes.iter() {
        let r = &mut y;
        r.cache.push(*c);
    }
}

fn main() {}
