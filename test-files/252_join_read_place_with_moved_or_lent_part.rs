//! Joins where one path holds a place for reading (shared-borrowed, or
//! unpacked because a part of it is shared-borrowed) and the other path has
//! moved out or lent a part of it.

struct T {
    n: i32,
}
struct S {
    v: T,
    w: T,
}
struct P {
    a: S,
    b: S,
}

fn consume<X>(_s: X) {}
fn read<X>(_s: &X) {}
fn mk() -> S {
    S {
        v: T { n: 1 },
        w: T { n: 2 },
    }
}
fn mkp() -> P {
    P { a: mk(), b: mk() }
}

// Borrowing `p.a.v` unpacks `p` for reading, so `p.a.w` has R although it is
// not borrowed. `p.a` is moved out on the other branch. The join unpacks that
// branch's W `p.a` to the same layout, and the edge from the borrowing branch
// drops the values of `p.a.v` and `p.a.w`: both are W after the join and do
// not regain capability later.
fn move_parent_or_borrow_field(c: bool) {
    let mut p = mkp();
    let o = T { n: 0 };
    let r;
    if c {
        consume(p.a);
        r = &o;
    } else {
        r = &p.a.v;
    }
    // PCG: bb3 -> bb5: unpack p.a with capability W
    // PCG: bb4 -> bb5: Restore capability E to p.a.w
    // PCG: bb4 -> bb5: Weaken(Weaken { place: _2.0.1, from: E, to: W, for_storage_dead: false, _marker: PhantomData<&()> })
    // PCG: bb4 -> bb5: Restore capability E to p.a.v
    // PCG: bb4 -> bb5: Weaken(Weaken { place: _2.0.0, from: E, to: W, for_storage_dead: false, _marker: PhantomData<&()> })
    // PCG: bb5[0] pre_operands: p.a: W
    // ~PCG: bb6[0] pre_operands: Restore capability W to p.a.v
    // ~PCG: bb7[0] pre_main: Restore capability W to p.a.w
    read(r);
    p = mkp();
}

// The same join with the branches swapped, so that the W leaf and the R
// expansion meet from the other sides.
fn borrow_field_or_move_parent(c: bool) {
    let mut p = mkp();
    let o = T { n: 0 };
    let r;
    if c {
        r = &p.a.v;
    } else {
        consume(p.a);
        r = &o;
    }
    // PCG: bb2 -> bb5: Restore capability E to p.a.w
    // PCG: bb2 -> bb5: Weaken(Weaken { place: _2.0.1, from: E, to: W, for_storage_dead: false, _marker: PhantomData<&()> })
    // PCG: bb2 -> bb5: Restore capability E to p.a.v
    // PCG: bb2 -> bb5: Weaken(Weaken { place: _2.0.0, from: E, to: W, for_storage_dead: false, _marker: PhantomData<&()> })
    // PCG: bb4 -> bb5: unpack p.a with capability W
    // PCG: bb5[0] pre_operands: p.a: W
    // ~PCG: bb6[0] pre_operands: Restore capability W to p.a.v
    // ~PCG: bb7[0] pre_main: Restore capability W to p.a.w
    read(r);
    p = mkp();
}

// `p.a` and `p.a.v` are both borrowed on the `else` branch, and `p.a` is
// moved out on the other. The edge from the borrowing branch drops the values
// of `p.a.v` and `p.a.w`, so both borrows are labelled with their values at
// the end of that branch, and the current `p.a` is W.
fn move_parent_or_borrow_parent_and_field(c: bool) {
    let mut p = mkp();
    let os = mk();
    let o = T { n: 0 };
    let q;
    let r;
    if c {
        consume(p.a);
        q = &os;
        r = &o;
    } else {
        q = &p.a;
        r = &p.a.v;
    }
    // PCG: bb4 -> bb6: unpack p.a with capability W
    // PCG: bb5 -> bb6: Restore capability E to p.a.w
    // PCG: bb5 -> bb6: Weaken(Weaken { place: _2.0.1, from: E, to: W, for_storage_dead: false, _marker: PhantomData<&()> })
    // PCG: bb5 -> bb6: Restore capability E to p.a.v
    // PCG: bb5 -> bb6: Weaken(Weaken { place: _2.0.0, from: E, to: W, for_storage_dead: false, _marker: PhantomData<&()> })
    // PCG: bb6[0] pre_operands: borrow: _14 before bb5[6]:PreMain = & p.a after bb5 under conditions bb2 -> bb5
    // PCG: bb6[0] pre_operands: borrow: _16 before bb5[13]:PreMain = & p.a.v after bb5 under conditions bb2 -> bb5
    // PCG: bb6[0] pre_operands: p.a: W
    read(q);
    read(r);
    p = mkp();
}

// `p.a` and `p.a.v` are both borrowed on the `else` branch, and `p.a.v` is
// moved out on the other. The edge from the borrowing branch drops the value
// of `p.a.v`, so both borrows are labelled with their values at the end of
// that branch, and the current `p.a.w` keeps its value. `p.a.w` is E while `q`
// is live: the borrow refers to the labelled value, and its expiry cannot
// reach the current places through the label.
fn move_field_or_borrow_parent_and_field(c: bool) {
    let mut p = mkp();
    let os = mk();
    let o = T { n: 0 };
    let q;
    let r;
    if c {
        consume(p.a.v);
        q = &os;
        r = &o;
    } else {
        q = &p.a;
        r = &p.a.v;
    }
    // PCG: bb5 -> bb6: Restore capability E to p.a.v
    // PCG: bb5 -> bb6: Weaken(Weaken { place: _2.0.0, from: E, to: W, for_storage_dead: false, _marker: PhantomData<&()> })
    // PCG: bb6[0] pre_operands: borrow: _14 before bb5[6]:PreMain = & p.a after bb5 under conditions bb2 -> bb5
    // PCG: bb6[0] pre_operands: borrow: _16 before bb5[13]:PreMain = & p.a.v after bb5 under conditions bb2 -> bb5
    // PCG: bb6[0] pre_operands: p.a.v: W
    // PCG: bb6[0] pre_operands: p.a.w: E
    read(q);
    read(r);
    p = mkp();
}

fn main() {}
