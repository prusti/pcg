enum S {
    Left(String),
    Right(String),
}

fn f(mut s: S) {
    let mut x = String::new();
    let mut rx = &mut x;
    let mut y = String::new();
    match s {
        S::Left(mut left) => {
            rx = &mut left;
        }
        S::Right(mut right) => {
            y = right;
        }
    }
    // rx will not survive the branch, it's partially moved
}

struct Guard<'a>(&'a mut u32);

impl Drop for Guard<'_> {
    fn drop(&mut self) {
        *self.0 += 1;
    }
}

fn consume(_g: Guard<'_>) {}

fn read<T>(_t: &T) {}

// The destructor of `g` uses its loan of `x`, so the loan lasts until the drop
// of `g`, and `g` keeps its value until then.
fn guard_kept_until_drop() -> u32 {
    // `bb1[4]` drops `g`.
    // ~PCG: bb1[0] pre_operands: Restore capability E to x
    // PCG: bb1[4] pre_main: g: E
    // PCG: bb2[0] pre_operands: Restore capability E to x
    let mut x = 0;
    {
        let g = Guard(&mut x);
        read(&g);
    }
    x
}

// As above, with `g` moved out on one path: its drop at the end of the block
// still uses the loan on the other.
fn guard_moved_on_one_path(c: bool) -> u32 {
    // `bb3` is the path that keeps `g`, and `bb4[1]` drops it.
    // ~PCG: bb3[0] pre_operands: Weaken g from E to W
    // ~PCG: bb3[0] pre_operands: Restore capability E to x
    // PCG: bb5[0] pre_operands: Restore capability E to x
    let mut x = 0;
    {
        let g = Guard(&mut x);
        if c {
            consume(g);
        }
    }
    x
}

// The destructor of a `Vec` may not use the loans of its elements
// (`#[may_dangle]`), so the loan of `x` ends at the last use of `v`; `v` keeps
// its value until its drop.
fn vec_of_loans_until_drop() -> u32 {
    // `bb3[2]` assigns `x` and `bb3[4]` drops `v`.
    // PCG: bb3[2] pre_operands: Restore capability E to x
    // ~PCG: bb3[2] pre_operands: Weaken v from E to W
    // PCG: bb3[4] pre_main: v: E
    let mut x = 0;
    let v = vec![&mut x];
    x = 1;
    x
}

// `total` is still to be dropped after the loop, so leaving the loop does not
// weaken it.
fn value_dropped_after_loop<X: Clone>(xs: &[X], t: &X) {
    // `bb9` leaves the loop, and `bb9[6]` drops `total`.
    // ~PCG: bb9[0] pre_operands: Weaken total from E to W
    // PCG: bb9[0] pre_operands: total: E
    // PCG: bb9[6] pre_main: total: E
    let total = t.clone();
    for x in xs {
        read(x);
        read(&total);
    }
}

// A reference whose lifetime projection is dead keeps its capability while it
// is part of a value with drop glue: the destructor of `s` needs all of it.
fn reference_in_value_with_drop_glue<'a>(mut s: Box<(&'a u32, &'a u32)>, x: &'a u32, c: bool) {
    // `bb1[2]` assigns `s.1` and `bb3[1]` drops `s`.
    // ~PCG: bb1[3] pre_operands: Weaken (*s).1 from E to W
    // PCG: bb3[0] pre_operands: s: E
    if c {
        s.1 = x;
    }
}

// A value without drop glue keeps its capability after its last use until its
// StorageDead.
fn no_drop_glue_after_last_use() -> u32 {
    // PCG: bb1[7] post_main: n: E
    // PCG: bb1[8] pre_main: Weaken(Weaken { place: _1, from: E, to: W, for_storage_dead: true, _marker: PhantomData<&()> })
    let n = 1;
    read(&n);
    let m = 2;
    m
}

fn main() {
    let s = S::Left("Hello".to_string());
}
