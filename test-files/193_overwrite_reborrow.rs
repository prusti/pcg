fn main() {
    let mut one = 2; let mut two = 2;

    let mut y = &mut one;
    let z = &mut (*y);
    y = &mut two;

    *z = 4;
}

// `*x` is lent to `r`, which is dead at the write, but the loan stays in the
// graph while `t`, a reborrow through the shared reference `*r`, lives. The
// write moves the loan to the old value of `*x`, so `*x` gets W.
fn overwrite_lent_through_shared_reborrow<'a>(x: &mut &'a u32) {
    // PCG: bb0[12] pre_main: Label place *x (Write)
    // PCG: bb0[12] pre_main: Restore *x to W
    let r = &mut *x;
    let t: &'a u32 = &**r;
    *x = t;
}

// The same for an owned place.
fn overwrite_owned_lent_through_shared_reborrow<'a>(mut x: &'a u32) -> &'a u32 {
    // PCG: bb0[12] pre_main: Restore capability W to x
    let r = &mut x;
    let t: &'a u32 = &**r;
    x = t;
    x
}
