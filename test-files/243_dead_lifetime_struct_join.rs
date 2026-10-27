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

fn main() {}
