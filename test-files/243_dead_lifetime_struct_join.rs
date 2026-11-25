// PCG_EXPECTED_FAILURE: frame boxed_part_lent_or_moved
// PCG_EXPECTED_FAILURE: frame boxed_part_lent_or_uninit
// PCG_EXPECTED_FAILURE: frame boxed_referent_lent_part_frozen
// PCG_EXPECTED_FAILURE: label Ctx::row
// PCG_EXPECTED_FAILURE: label arg
// PCG_EXPECTED_FAILURE: label boxed_frozen_part
// PCG_EXPECTED_FAILURE: label boxed_part_lent_or_moved
// PCG_EXPECTED_FAILURE: label boxed_part_lent_or_uninit
// PCG_EXPECTED_FAILURE: label boxed_referent_lent_part_frozen
// PCG_EXPECTED_FAILURE: label local
// PCG_EXPECTED_FAILURE: remove-edge boxed_part_lent_or_moved
// PCG_EXPECTED_FAILURE: remove-edge boxed_part_lent_or_uninit
// PCG_EXPECTED_FAILURE: remove-edge boxed_referent_lent_part_frozen
// A struct whose lifetime is dead on one branch must still join with a branch
// that reads through it.
struct Ctx {
    r: i32,
}

impl Ctx {
    fn row(&self) -> &i32 {
        &self.r
    }
}

struct T<'a> {
    ctx: &'a mut Ctx,
    valid: bool,
}

fn arg<'a>(t: T<'a>) -> Option<&'a i32> {
    // PCG: bb3[0] pre_operands: Weaken t from E to W
    if t.valid { Some(t.ctx.row()) } else { None }
}

fn local<'a>(t: T<'a>) -> Option<&'a i32> {
    // `u` is W on the `else` branch and read-expanded on the other: the read
    // path labels the value of `u` that the result borrows from, unfreezes
    // `u` and weakens it to W.
    // PCG: bb3[0] pre_operands: Weaken u from E to W
    // PCG: bb2 -> bb4: Label place u (Write)
    // PCG: bb2 -> bb4: Unfreeze u
    // PCG: bb2 -> bb4: Weaken u from E to W
    // PCG: bb4[0] pre_operands: u: W
    // ~PCG: bb4[0] pre_operands: u: R
    let u = t;
    if u.valid { Some(u.ctx.row()) } else { None }
}

// `s` is W on the `else` branch, and unpacked by the write to its contents on
// the other. A Box at W gives its contents nothing, so the join holds `s`
// packed at W: the writing path weakens the contents and packs them.
fn boxed<'a>(mut s: Box<(&'a u32, &'a u32)>, x: &'a u32, c: bool) {
    // PCG: bb2[0] pre_operands: Weaken s from E to W
    // PCG: bb1 -> bb3: Weaken (*s).0 from E to W
    // PCG: bb3[0] pre_operands: s: W
    if c {
        s.1 = x;
    }
}

// As above, with a variant of the Box's contents unpacked: the paths meet at
// the Box, not at the enum.
fn boxed_variant<'a>(s: Box<Option<(&'a u32, String)>>, c: bool) {
    // PCG: bb6 -> bb8: Collapse(RepackCollapse { to: _1, capability: W, guide: None, _marker: PhantomData<&()> })
    // PCG: bb8[0] pre_operands: s: W
    if c {
        if let Some((_, t)) = *s {
            drop(t);
        }
    }
}

// As `boxed`, with a part of the contents frozen while `r` borrows its
// referent. Packing the contents at W labels them, which moves the loan to
// the old referent and ends the freeze.
fn boxed_frozen_part<'a>(mut s: Box<(&'a u32, &'a u32)>, x: &'a u32, c: bool) -> u32 {
    // PCG: bb1 -> bb3: Unfreeze (*s).0
    // PCG: bb1 -> bb3: Weaken (*s).0 from E to W
    // PCG: bb3[0] pre_operands: s: W
    let z = 0;
    let mut r = &z;
    if c {
        r = &*s.0;
        s.1 = x;
    }
    *r
}

// As `boxed`, with the referent of the reference in the Box mutably lent on
// one path. The loan lies behind the reference, so it does not keep `s` from
// being overwritten: the join holds `s` at W.
fn boxed_referent_lent<'a>(mut s: Box<&'a mut u32>, c: bool) -> u32 {
    // PCG: bb1 -> bb3: Weaken *s from e to W
    // PCG: bb3[0] pre_operands: s: W
    let mut z = 0;
    let r: &mut u32;
    if c {
        r = &mut **s;
    } else {
        r = &mut z;
    }
    *r += 1;
    0
}

// As above, with another part of the contents frozen for `r`: that loan
// keeps `s` from being overwritten, so the join does not hold `s`.
fn boxed_referent_lent_part_frozen<'a>(mut s: Box<(&'a mut u32, u32)>, c: bool, k: &'a mut u32) -> u32 {
    // PCG: bb1 -> bb4: Weaken suspended s from E to W
    // ~PCG: bb4[0] pre_operands: s: W
    let r;
    let r2: &mut u32;
    let z = 5;
    if c {
        r = &s.1;
        r2 = &mut *s.0;
    } else {
        drop(s);
        r = &z;
        r2 = k;
    }
    *r2 += 1;
    *r
}

// `s` is frozen for a loan of a part of its contents on one path and moved
// out on the other. The loan keeps the join from holding `s`; both paths
// lend `s` whole, recording W, since a Box at W has no contents to lend
// apart. When the loan ends, `s` gets W back.
fn boxed_part_lent_or_moved(s: Box<(u32, u32)>, c: bool) -> u32 {
    // PCG: bb1 -> bb4: Weaken suspended s from E to W
    // PCG: bb4[0] pre_operands: s: suspended W
    // PCG: bb4[3] pre_operands: s: W
    let r;
    let k = 5;
    if c {
        r = &s.0;
    } else {
        drop(s);
        r = &k;
    }
    *r
}

// As above, with `s` uninitialised on the other path and the loan used in a
// loop after the join.
fn boxed_part_lent_or_uninit(c: bool, n: u32) -> u32 {
    // PCG: bb7[0] pre_operands: s: suspended W
    // PCG: bb13[0] pre_operands: s: W
    let z = 0;
    let s: Box<(u32, u32)>;
    let r: &u32;
    if c {
        s = Box::new((1, 2));
        r = &s.0;
    } else {
        r = &z;
    }
    let mut i = 0;
    let mut acc = 0;
    while i < n {
        acc += *r;
        i += 1;
    }
    acc
}

fn main() {}
