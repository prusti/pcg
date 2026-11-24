// At a loop head, the referents of a place's mutable references are reported
// as its lifetime projections, apart from the place itself, unless the loop
// writes the place's own value.

struct R<'a> {
    r: &'a mut u32,
}

fn writes_through(x: &mut u32, cont: bool) {
    // PCG: bb1 loop invariant: x: R
    // PCG: bb1 loop invariant: x↓'?3: E
    while cont {
        *x += 1;
    }
}

fn reads_through_field(s: R<'_>, cont: bool) -> u32 {
    let mut n = 0;
    // PCG: bb1 loop invariant: s.r: R
    // PCG: bb1 loop invariant: s.r↓'?4: R
    while cont {
        n = *s.r;
    }
    n
}

// A write behind two references writes the referent of the inner one and only
// reads that of the outer one, the inner reference.
fn writes_nested(x: &mut &mut u32, cont: bool) {
    // PCG: bb1 loop invariant: x: R
    // PCG: bb1 loop invariant: x↓'?4: R
    // PCG: bb1 loop invariant: x↓'?5: E
    while cont {
        **x += 1;
    }
}

fn inc(r: &mut &mut u32) {
    **r += 1;
}

// Passing on a mutable borrow of `*x` may also change what `*x` refers to.
fn passes_nested(x: &mut &mut u32, cont: bool) {
    // PCG: bb1 loop invariant: x: R
    // PCG: bb1 loop invariant: x↓'?5: E
    // PCG: bb1 loop invariant: x↓'?6: E
    // ~PCG: bb1 loop invariant: x↓'?6: R
    while cont {
        inc(x);
    }
}

fn fresh<'b>() -> &'b mut u32 {
    Box::leak(Box::new(0))
}

// Assigning a reference behind `x` changes what it refers to.
fn assigns_behind(x: &mut R<'_>, cont: bool) {
    // PCG: bb1 loop invariant: x↓'?7: W
    // PCG: bb1 loop invariant: x↓'?8: W
    // ~PCG: bb1 loop invariant: x↓'?8: R
    while cont {
        x.r = fresh();
    }
}

struct Named<'a> {
    name: &'static str,
    r: &'a mut u32,
}

// Assigning `x.name` writes the referent of `x`, but not what the `'static`
// reference refers to, which no lifetime projection of `x` holds; `x`'s other
// projection stays at `R`.
fn assigns_static(x: &mut Named<'_>, cont: bool) {
    // PCG: bb1 loop invariant: x: R
    // PCG: bb1 loop invariant: x↓'?6: W
    // PCG: bb1 loop invariant: x↓'?7: R
    while cont {
        x.name = "a";
    }
}

// A loop that uses nothing behind the references of a place leaves their
// referents unchanged.
fn reads_whole(s: R<'_>, cont: bool) {
    // PCG: bb1 loop invariant: s: R
    // PCG: bb1 loop invariant: s↓'?6: R
    while cont {
        std::hint::black_box(&s);
    }
}

// A loop that writes the reference itself requires it at `E`, which covers its
// referent.
fn reassigns(mut x: &mut u32, cont: bool) {
    // PCG: bb1 loop invariant: x: E
    // ~PCG: bb1 loop invariant: x: R
    while cont {
        *x += 1;
        x = fresh();
    }
}

// A loop that also reads the place behind `x` as a whole may read the referent
// it writes, so it is required at `E`.
fn writes_and_reads_behind(x: &mut &mut u32, cont: bool) {
    // PCG: bb1 loop invariant: x↓'?7: R
    // PCG: bb1 loop invariant: x↓'?8: E
    // ~PCG: bb1 loop invariant: x↓'?8: W
    while cont {
        std::hint::black_box(&*x);
        **x = 1;
    }
}

// A loop that also reads the holder as a whole may read the referents it
// writes, so they are required at `E`.
fn writes_and_reads_whole(x: &mut u32, cont: bool) {
    // PCG: bb1 loop invariant: x: R
    // PCG: bb1 loop invariant: x↓'?6: E
    // ~PCG: bb1 loop invariant: x↓'?6: W
    while cont {
        *x = 1;
        std::hint::black_box(&x);
    }
}

fn main() {}
