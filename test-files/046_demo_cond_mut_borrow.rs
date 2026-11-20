fn f(c: bool){
    let mut x = 1;
    let mut y = 2;
    let mut r = if c {
        &mut x
    } else {
        &mut y
    };
    *r = 7;
    x += 1;
    // Each branch lends the place borrowed in the other branch to that
    // borrow, which gives it back when it expires.
    // PCG: bb1 -> bb3: Lend y to borrow: _6 before bb2[3]:PreMain <before bb2[2]:PreOperands> = &mut  y under conditions bb0 -> bb2
    // PCG: bb2 -> bb3: Lend x to borrow: r = &mut  x under conditions bb0 -> bb1
    // PCG: bb3[3] pre_operands: Remove Edge borrow: r = &mut  x under conditions bb0 -> bb1 returning E to x
    // `r` is weakened once, when its borrow expires.
    // PCG: bb3[3] pre_operands: Weaken r from E to W
    // ~PCG: bb3[3] pre_operands: Weaken r from W to W
}

fn main(){
}
