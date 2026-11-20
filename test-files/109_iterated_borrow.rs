struct T {}
fn main () {}
fn test(b: bool) {
    let mut t = T {};
    let mut x : &mut T = &mut t; // x -> t
    let y : &mut (&mut T) = &mut x; // y -> x -> t
    let test_y = y; // test_y -> x -> t
    // text_y should be dead, x should become accessible
    // x -> t, and the snapshot of x's lifetime projection taken when `y`
    // borrowed `x` is merged back into it
    // PCG: bb0[20] post_main: borrow: x = &mut  (*_4) before bb0[9]:PreMain
    // ~PCG: bb0[20] post_main: x↓'?6 before bb0[12]:PostMain -> x↓'?6
    let test_x = x; // test_x -> t
    // test_x should be dead,
    let test_t = t;
}

struct P<'a>(&'a mut u32);

impl<'a> P<'a> {
    fn reborrow(&mut self) -> P<'_> {
        P(&mut *self.0)
    }
}

fn check(p: P<'_>) -> bool {
    *p.0 > 0
}

fn repeated_reborrows(c: P<'_>) -> bool {
    // PCG_LIFETIME_DISPLAY: c 0 'c
    let mut c = c;
    // After two reborrows of `c` have ended, the snapshots of `c`'s lifetime
    // projection that they took are merged into it: the argument and the
    // reborrows flow into the current projection directly.
    // PCG: bb6[0] pre_operands: c before bb0[1]:PostOperands↓'c -> c↓'?10 under conditions bb2 -> bb3, bb5 -> bb6
    // PCG: bb6[0] pre_operands: _5 before bb0[7]:PostOperands↓'?13 -> c↓'?10 under conditions bb2 -> bb3, bb5 -> bb6
    // PCG: bb6[0] pre_operands: _8 before bb3[5]:PostOperands↓'?16 -> c↓'?10 under conditions bb2 -> bb3, bb5 -> bb6
    // ~PCG: bb6[0] pre_operands: c↓'?10 before bb3[4]:PostMain -> c↓'?10 under conditions bb2 -> bb3, bb5 -> bb6
    check(c.reborrow()) && check(c.reborrow()) && check(c.reborrow())
}
