struct T {
    f: u32,
}

struct H {
    g: T,
}

// The read of `a` and the exclusive use of `a.g.f` both require a
// capability for the packed place `a` at the loop head.
fn read_and_exclusive(mut a: H, cont: bool) -> H {
    // PCG: bb1[0] pre_operands: a: E
    // PCG: bb1 loop invariant: a: E
    // ~PCG: bb1 loop invariant: a: R
    while cont {
        std::hint::black_box(&a);
        a.g.f += 1;
    }
    a
}

// Read and write requirements must combine into exclusive capability,
// regardless of the iteration order of the place usages.
fn read_and_write(mut a: H, cont: bool) -> H {
    // PCG: bb1[0] pre_operands: a: E
    // PCG: bb1 loop invariant: a: E
    // ~PCG: bb1 loop invariant: a: R
    // ~PCG: bb1 loop invariant: a: W
    while cont {
        std::hint::black_box(&a);
        a.g.f = 5;
    }
    a
}

fn read_only(a: H, cont: bool) -> H {
    // PCG: bb1 loop invariant: a: R
    // ~PCG: bb1 loop invariant: a: E
    while cont {
        std::hint::black_box(&a);
        std::hint::black_box(a.g.f);
    }
    a
}

fn write_only(mut a: H, cont: bool) -> H {
    // PCG: bb1 loop invariant: a.g.f: W
    // ~PCG: bb1 loop invariant: a.g.f: E
    while cont {
        a.g.f = 5;
    }
    a
}

fn consume(_s: String) {}

fn moved_in_loop(stop: bool) {
    // `s` is not definitely initialized at the loop head (bb2): the back edge
    // arrives with it moved out, so the loop head holds it with W and the
    // entry weakens it.
    // PCG: bb1 -> bb2: Weaken s from E to W
    // PCG: bb2[0] pre_operands: s: W
    let mut s = String::new();
    loop {
        s = String::from("x");
        consume(s);
        if stop {
            break;
        }
    }
}

// `x` is moved out on the back edge and frozen only on entry: the loop head
// holds it with W.
fn moved_in_loop_frozen_on_entry(c: bool) {
    // PCG: bb2 -> bb3: Weaken x from E to W
    // PCG: bb3[0] pre_operands: x: W
    let mut x = String::new();
    let y = String::new();
    let mut r = &x;
    loop {
        let _ = r.len();
        r = &y;
        x = String::new();
        drop(x);
        if c {
            break;
        }
    }
}

// `r` is moved out on the back edge while its referent is lent on entry.
fn moved_in_loop_lent_on_entry(x: &mut i32, y: &mut i32, c: bool) {
    // PCG: bb0 -> bb1: Weaken r from e to W
    // PCG: bb1[0] pre_operands: r: W
    let mut r = &mut *x;
    let mut rr = &mut *r;
    loop {
        *rr += 1;
        rr = &mut *y;
        r = &mut *x;
        let _r2 = r;
        if c {
            break;
        }
    }
}

// `t` is dead at the loop head and frozen on entry, while `r` borrows its
// referent. The loop overwrites `r`, which ends that loan and weakens `t`, so
// the loop head holds `t` with W and `r` borrows from the labelled `t`.
fn dead_frozen_on_entry(a: u32, y: &u32, n: u32) -> u32 {
    // PCG: bb0 -> bb1: Label place t (Write)
    // PCG: bb0 -> bb1: Weaken t from E to W
    // PCG: bb1[0] pre_operands: borrow: r = & *t loop bb1
    // PCG: bb1[0] pre_operands: t: W
    let t = &a;
    let mut r = &*t;
    let mut i = 0;
    while i < n {
        r = y;
        i += 1;
    }
    *r
}

// As above, with `rr` borrowing `t` itself: the loan keeps `t` from being
// overwritten, so the loop head cannot hold it with W. The loop may still
// end the loan, and the back edge then arrives with `t` weakened: the loop
// head lends `t` to the loan, recording W, and so does the back edge.
fn dead_borrowed_on_entry(a: u32, b: u32, n: u32) -> u32 {
    // PCG: bb0 -> bb1: Weaken suspended t from E to W
    // PCG: bb1[0] pre_operands: t: suspended W
    // ~PCG: bb1[0] pre_operands: t: W
    let t = &a;
    let tt = &b;
    let mut rr = &t;
    let mut i = 0;
    while i < n {
        rr = &tt;
        i += 1;
    }
    **rr
}

// As above, with the loan of `t` living through the loop: the loop head
// cannot tell, and lends `t` all the same.
fn dead_borrowed_through_loop(a: u32, n: u32) -> u32 {
    // PCG: bb0 -> bb1: Lend t to borrow: rr = & t
    // PCG: bb1[0] pre_operands: t: suspended W
    let t = &a;
    let rr = &t;
    let mut i = 0;
    let mut s = 0;
    while i < n {
        s += **rr;
        i += 1;
    }
    s
}

// A dead `x` whose referent is unpacked, with a part frozen for `r` and a
// part lent to `m`: weakening `x` labels its value, and the loans go with it.
fn dead_unpacked_on_entry<'a>(x: &mut (&'a u32, u32), n: u32) -> u32 {
    // PCG: bb1[0] pre_operands: borrow: r = & (*x).0 loop bb1
    // ~PCG: bb1[0] pre_operands: borrow: r = & (*x).0
    // PCG: bb1[0] pre_operands: x: W
    let m = &mut (*x).1;
    let r = &(*x).0;
    let mut i = 0;
    let mut s = 0;
    while i < n {
        s += **r;
        *m += 1;
        i += 1;
    }
    s + *m
}

// As `dead_borrowed_on_entry`, with `rr` borrowing `t` mutably: `t` is lent
// on entry, and the loop head records W for it.
fn dead_lent_on_entry(a: &mut u32, b: &mut u32, n: u32) -> u32 {
    // PCG: bb0 -> bb1: Weaken suspended t from E to W
    // PCG: bb1[0] pre_operands: t: suspended W
    let mut t = a;
    let mut tt = b;
    let mut rr = &mut t;
    let mut i = 0;
    while i < n {
        rr = &mut tt;
        i += 1;
    }
    **rr
}

// The dead `s` is frozen on entry while `r` borrows a part of it. The loan
// keeps `s` from being overwritten, so the loop head keeps it frozen.
fn dead_part_borrowed_on_entry(a: &u32, n: u32) -> u32 {
    // PCG: bb1[0] pre_operands: s: R
    // ~PCG: bb1[0] pre_operands: s: W
    let s = (a, 5u32);
    let r = &s.1;
    let mut i = 0;
    let mut acc = 0;
    while i < n {
        acc += *r;
        i += 1;
    }
    acc
}

// The dead `s` is unpacked on entry, its part `s.1` lent to `r`, which the
// loop overwrites. When that loan ends, `s.0`, whose lifetime is dead, is
// weakened: the loop head holds it with W.
fn dead_part_lent_on_entry(a: &u32, n: u32) -> u32 {
    // PCG: bb0 -> bb1: Weaken s.0 from E to W
    // PCG: bb1[0] pre_operands: s.0: W
    let mut s = (a, 5u32);
    let mut z = 3;
    let mut r = &mut s.1;
    let mut i = 0;
    while i < n {
        *r += 1;
        r = &mut z;
        i += 1;
    }
    *r
}

// `o` is written in the loop while `v` borrows into its referent. The loop
// may run zero times, so `o` stays lent at the loop head (its E recorded);
// the write in the loop labels the old referent, and `o` gets E back once
// `v` ends.
fn written_in_loop_lent_on_entry(
    mut o: Option<&mut (u32, u32)>,
    c: bool,
) -> Option<&mut (u32, u32)> {
    // PCG: bb6[0] pre_operands: o: suspended E
    // ~PCG: bb6[0] pre_operands: o: E
    // PCG: bb8[2] pre_main: Label place o (Write) returning E to o
    // PCG: bb8 -> bb6: Lend o to borrow: v before bb4[3]:PreMain <before bb4[2]:PreOperands> = &mut  (*o@Some.0).1 under conditions bb0 -> bb2
    // PCG: bb9[6] pre_operands: o: E
    let mut z = 0;
    let v: &mut u32 = match o {
        Some(&mut (_, ref mut v)) => v,
        None => &mut z,
    };
    while c {
        o = None;
    }
    *v = 1;
    o
}

// As above, with `v` a shared borrow: `o` is frozen on entry and stays frozen
// at the loop head. The write in the loop moves the loan to the old
// referent, which ends the freeze.
fn written_in_loop_frozen_on_entry(x: &mut (u32, u32), c: bool) -> u32 {
    // PCG: bb6[0] pre_operands: o: R
    // PCG: bb6[0] pre_operands: o: suspended E
    // ~PCG: bb6[0] pre_operands: o: E
    // PCG: bb8[2] pre_main: Label place o (Write)
    // PCG: bb8[2] pre_main: Unfreeze o
    // PCG: bb8 -> bb6: Freeze o
    let mut o = Some(x);
    let v = match o {
        Some(&mut (_, ref v)) => Some(v),
        None => None,
    };
    while c {
        o = None;
    }
    let k = v.map_or(0, |v| *v);
    match o {
        Some(r) => r.0 + k,
        None => k,
    }
}

fn main() {}
