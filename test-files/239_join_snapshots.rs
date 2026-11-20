#![feature(box_patterns)]

struct Node {
    next: Option<Box<Node>>,
}

fn snapshot_before_join_weakening(mut node: Node) {
    // PCG: bb4[4] post_main: x: e
    // PCG: bb4 -> bb5: Weaken x from e to W
    // PCG: bb5[0] pre_operands: x: W

    // We use after bb4 instead of before bb5 because Prusti can refer to the version of `x` after bb4:
    // before bb5, the weaken has already occurred and x is inaccessible.
    // PCG: bb5[0] pre_operands: {*x after bb4} -> {(*x).next after bb4} under conditions bb0 -> bb2
    // ~PCG: bb5[0] pre_operands: {*x before join bb5} -> {(*x).next before join bb5} under conditions bb0 -> bb2
    let mut x = &mut node;
    x = match x.next {
        Some(box ref mut next) => next,
        None => x,
    };
    x.next = None;
}

enum Next {
    Left(Box<BranchNode>),
    Right(Box<BranchNode>),
    None,
}

struct BranchNode {
    next: Next,
}

fn snapshots_from_multiple_predecessors(mut node: BranchNode) {
    // Each borrowed arm must retain its own snapshot and branch condition.
    // PCG: bb5[4] post_main: x: e
    // PCG: bb6[4] post_main: x: e
    // PCG: bb5 -> bb7: Weaken x from e to W
    // PCG: bb6 -> bb7: Weaken x from e to W
    // PCG: bb7[0] pre_operands: x: W
    // PCG: bb7[0] pre_operands: {*x after bb5} -> {(*x).next after bb5} under conditions bb0 -> bb3
    // PCG: bb7[0] pre_operands: {*x after bb6} -> {(*x).next after bb6} under conditions bb0 -> bb2
    let mut x = &mut node;
    x = match x.next {
        Next::Left(box ref mut next) => next,
        Next::Right(box ref mut next) => next,
        Next::None => {
            // Move x through a tuple to prevent an implicit reborrow.
            let moved = (x,);
            moved.0
        }
    };
    x.next = Next::None;
}

struct RawCell {
    p: *mut i32,
    n: i32,
}

// The dereference of a raw pointer is an unpacking, not a loan: the path
// that read it directly packs it once the read is done, dropping what its
// referent was read with, before the join.
unsafe fn raw_deref_read_or_frozen(mut s: RawCell, c: bool) -> i32 {
    // PCG: bb2[2] pre_operands: Remove Edge {s.p} -> {*s.p} under conditions bb0 -> bb2
    // PCG: bb2[2] pre_operands: Unfreeze s
    // ~PCG: bb2 -> bb3: Label place *s.p (Detach)
    let v;
    if c {
        let q = &s;
        v = *(*q).p;
    } else {
        v = *s.p;
    }
    s.n = v;
    s.n
}

// A part of the referent of a raw pointer is borrowed for read, then the
// pointer is overwritten. The dereference unpacks `p`, so `p` stays frozen
// while the borrow lives; the write labels the old referent with what it
// holds, and `p` is unfrozen whole.
unsafe fn raw_referent_part_read_pointer_overwritten(x: *mut (u32, u32), y: *mut (u32, u32)) -> u32 {
    // PCG: bb0[5] post_main: p: R
    // PCG: bb0[8] pre_main: Unfreeze p
    // PCG: bb0[8] post_main: p: E
    let mut p = x;
    let r = &(*p).1;
    p = y;
    (*p).1 = 3;
    *r
}

// Writing a part of the referent of a raw pointer leaves the other part
// initialised: as for a reference, the dereference gives the referent E,
// not the W the write obtains.
unsafe fn raw_referent_part_written_sibling_read(p: *mut (u32, u32)) -> u32 {
    // PCG: bb0[0] pre_main: Add Edge {p} -> {*p} setting *p: E
    // PCG: bb0[1] pre_operands: (*p).1: R
    (*p).0 = 3;
    (*p).1
}

// As above, with the borrow on one path only. The loan behind the raw
// pointer is not in the value of `p`, so the join holds `p` at the meet W
// of the frozen and the uninitialised `p`.
unsafe fn raw_referent_part_read_on_one_path(x: *mut (u32, u32), c: bool) -> u32 {
    // PCG: bb1 -> bb3: Weaken p from E to W
    // PCG: bb3[0] pre_operands: p: W
    let mut p: *mut (u32, u32);
    let r: &u32;
    let y = 0;
    if c {
        p = x;
        r = &(*p).1;
    } else {
        r = &y;
    }
    p = x;
    let s = (*p).0;
    *r + s
}

// The pointer is frozen on both paths, and its referent borrowed on one.
// That path detaches the borrowed referent: the join holds `p` frozen, and
// with no loan in its value, `p` is unfrozen after the join.
unsafe fn raw_referent_part_read_on_one_path_frozen(p: *mut (u32, u32), c: bool) -> u32 {
    // PCG: bb1 -> bb3: Label place *p (Detach)
    // ~PCG: bb1 -> bb3: Unfreeze p
    // PCG: bb3[0] pre_operands: Unfreeze p
    let y = 0;
    let r: &u32;
    if c {
        r = &(*p).1;
    } else {
        r = &y;
    }
    *r + (*p).0
}

// A struct with a raw pointer field, read through the pointer on one path
// and frozen whole on both. The referent of the pointer is not part of the
// struct's value, so its record does not split the struct's: the join
// records `s` whole. The path that read through the pointer detaches the
// borrowed referent, so no loan keeps `s` frozen after the join.
unsafe fn raw_field_referent_read_on_one_path(s: (*mut (u32, u32), u32), c: bool) -> u32 {
    // PCG: bb1 -> bb3: Label place *s.0 (Detach)
    // ~PCG: bb1 -> bb3: Weaken suspended s.1 from E to None
    // PCG: bb3[0] pre_operands: Unfreeze s
    // PCG: bb3[0] pre_operands: s: E
    // ~PCG: bb3[0] pre_operands: s.0: suspended E
    let y = 0;
    let r: &u32;
    if c {
        r = &(*s.0).1;
    } else {
        r = &y;
    }
    *r + s.1
}

enum Two {
    None,
    A(u32),
    B(u32),
}

// Each path borrows a different variant of the referent of a shared
// reference field of the frozen `s`. Both paths record `s` whole; the
// referent is covered by that record, so the join keeps the record at `s`
// instead of splitting it to record the referent apart.
fn shared_referent_variant_on_each_path<'a>(s: (u32, &'a Two)) -> (u32, (u32, &'a Two)) {
    // ~PCG: bb4 -> bb6: Weaken suspended s.0 from E to None
    // ~PCG: bb5 -> bb6: Weaken suspended s.0 from E to None
    // PCG: bb6[0] pre_operands: s: suspended E
    // PCG: bb6[1] pre_operands: Unfreeze s
    // PCG: bb6[1] pre_operands: s: E
    let b = match s.1 {
        Two::A(x) | Two::B(x) => *x,
        _ => 0,
    };
    (b, s)
}

struct Bufs {
    bufs: Vec<u32>,
}

fn matches_zero(x: &u32) -> bool {
    *x == 0
}

fn take<B>(_b: B) {}

// A path whose guard failed has no loan left and holds `s` with E; the
// other path still lends a field of `*s`. The referent of `s` is unpacked
// and that field is lent to the other path's loan, so `s` gets E back when
// the loan ends.
fn guard_failed_or_field_lent(s: &mut Bufs) -> u32 {
    // PCG: bb8 -> bb3: Lend (*s).bufs to borrow: _5 before bb0[5]:PostOperands <before bb0[5]:PostMain> = &mut  (*s).bufs
    // ~PCG: bb8 -> bb3: Weaken s from E to e
    // PCG: bb3[0] pre_operands: s: E
    match s.bufs.first_mut() {
        Some(front) if matches_zero(front) => *front,
        _ => {
            take(s);
            0
        }
    }
}

fn main() {}
