//! Building a closure moves its captures into it. A capture of `&mut y` keeps
//! `y` borrowed as long as the closure is live, so the borrow must flow into
//! the closure rather than end with the capture's temporary.

fn capture_mut() {
    let mut y = 0;
    let mut c = || y = 1;
    // PCG: bb0[6] post_main: Add Edge _3 before bb0[6]:PostOperands↓'?7 -> c↓'?6
    // ~PCG: bb0[7] post_main: y: E
    // ~PCG: bb0[11] post_main: y: E
    c();
    let z = y;
}

fn main() {}
