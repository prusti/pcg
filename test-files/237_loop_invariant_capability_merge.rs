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

fn main() {}
