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

fn main() {}
