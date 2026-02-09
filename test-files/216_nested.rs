fn main() {
    let mut a = 1;
    let mut b = 2;
    let mut x = 10;
    let mut y = &mut x;            // x borrowed (by *y) for `a;
    let mut z = &mut y;            // y borrowed (by *z) for `b; `a outlive `b
    let mut w = &mut (**z);        // **z borrowed (by *w) for `c; `b outlive `c
    // borrowed: x, y, **z;  `a : `b : `c
    *z = &mut a;     // This is allowed:  // `b still lives
// PCG: bb0[22] post_main: *z↓'?9 -> z↓'?9 FUTURE
// PCG: bb0[22] post_main: _7 before bb0[22]:PostOperands↓'?11 -> *z↓'?9
    // y = &mut b; // This is not allowed // `b not alive
    let baz = *w;                   // `c alive(3/4)
}
