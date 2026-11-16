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

fn main() {}
