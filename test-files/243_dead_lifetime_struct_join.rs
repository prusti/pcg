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
    // `u` is W on the `else` branch and read-expanded on the other, so the
    // join leaves it without capability until its StorageDead.
    // PCG: bb3[0] pre_operands: Weaken u from E to W
    // ~PCG: bb4[0] pre_operands: u: W
    // ~PCG: bb4[0] pre_operands: u: R
    // PCG: bb3 -> bb4: Weaken u.ctx from W to None
    // PCG: bb4[1] pre_main: Label place u (Write) setting u.ctx: W, u.valid: W
    let u = t;
    if u.valid { Some(u.ctx.row()) } else { None }
}

fn main() {}
