fn main() {
    let mut a = 1;
    let mut b = 2;
    let mut x = 10;
    let mut y = &mut x;            // x borrowed (by *y) for `a;
    let mut z = &mut y;            // y borrowed (by *z) for `b; `a outlive `b
    let mut w = &mut (**z);        // **z borrowed (by *w) for `c; `b outlive `c
    // borrowed: x, y, **z;  `a : `b : `c
    *z = &mut a;     // This is allowed:  // `b still lives
    // y = &mut b; // This is not allowed // `b not alive
    println!("{}", *w);                   // `c alive(3/4)
}
