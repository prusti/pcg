struct List<T> {
    head: T,
    tail: Option<Box<List<T>>>,
}

impl<T> List<T> {
    fn new() -> Self {
        todo!()
    }
    fn push(&mut self, x: T) {
    }
    fn pop(&mut self) -> T {
        todo!()
    }
}

// fn f<'a>(mut ol1: List<&'a mut i32>, mut ol2: List<&'a mut i32>) {
//     let mut l1 = &mut ol1;
//     let mut l2 = &mut ol2;
//     while true {
//         let h = l1.pop();
//         l2.push(h);
//     }
// }

fn main() {
    let mut x = 0;
    let mut l1: List<&mut i32> = List::new(); // PCG_LIFETIME_DISPLAY: l1 0 'a
    let mut l2: List<&mut i32> = List::new(); // PCG_LIFETIME_DISPLAY: l2 0 'a
    let mut rl: &mut List<&mut i32> = &mut l1;
    while true {
        rl = &mut l2;
    }
    rl.push(&mut x);
    // let y = *rl1.pop();
}

// The back edge to the loop head snapshots `v`'s lifetime projection for the
// next iteration, while the snapshot taken at the start of this iteration is
// still in the graph. On the path without the push, the current projection is
// that snapshot's direct future (the path does not change it); the two must
// stay distinct nodes.
fn push_on_one_path<'a>(v: &mut Vec<&'a u32>, xs: &'a [u32]) {
    for x in xs {
        if *x > 3 {
            v.push(x);
        }
    }
}

// The same in a `while let` loop inside a closure, where the captured `packed`
// is written on only one path.
fn closure_writes_on_one_path(items: &[u32]) -> bool {
    let mut packed = false;
    let mut f = |input: &mut std::slice::Iter<'_, u32>| {
        while let Some(t) = input.next() {
            if *t == 3 {
                packed |= true;
            }
        }
    };
    f(&mut items.iter());
    packed
}

struct Pair<'a> {
    n: i32,
    r: &'a i32,
}

// Checks that the graph after the loop-head join is valid when a borrow of
// `t.0` is held across a loop that writes `t.1`. On the path into the loop, the
// borrow has replaced the lifetime projections of `*t` by placeholders, while
// the places the loop head obtains still have their current versions.
fn write_sibling_in_loop<'a>(t: &mut (Pair<'a>, Pair<'a>), y: &'a i32, mut k: u32) {
    let p = &mut t.0;
    while k > 0 {
        t.1.r = y;
        k -= 1;
    }
    p.n = 1;
}

// As `write_sibling_in_loop`, but a `for` loop also writes through the held
// borrow `p`, and `p` is not used after the loop.
fn write_through_borrow_and_sibling_in_loop<'a>(t: &mut (Pair<'a>, Pair<'a>), ys: &'a [i32]) {
    let p = &mut t.0;
    for y in ys {
        p.r = y;
        t.1.r = y;
    }
}

// As `write_sibling_in_loop`, with two paths into the loop that both hold the
// borrow, only one of which has already written the sibling.
fn write_sibling_in_loop_two_entries<'a>(
    t: &mut (Pair<'a>, Pair<'a>),
    y: &'a i32,
    mut k: u32,
    c: bool,
) {
    let p;
    if c {
        p = &mut t.0;
        t.1.r = y;
    } else {
        p = &mut t.0;
    }
    while k > 0 {
        t.1.r = y;
        k -= 1;
    }
    p.n = 1;
}

// As `write_sibling_in_loop`, where only one of two paths into the loop holds
// the borrow.
fn write_sibling_in_loop_one_entry_holds<'a>(
    t: &mut (Pair<'a>, Pair<'a>),
    y: &'a i32,
    mut k: u32,
    c: bool,
) {
    let mut p = None;
    if c {
        p = Some(&mut t.0);
    }
    while k > 0 {
        t.1.r = y;
        k -= 1;
    }
    if let Some(p) = p {
        p.n = 1;
    }
}

// The loop writes through both variants of `*r`, and the join at the loop head
// must stay valid.
fn push_into_variants<'a>(r: &mut Result<Vec<&'a u32>, Vec<&'a u32>>, xs: &'a [u32]) {
    for x in xs {
        match r {
            Ok(v) => v.push(x),
            Err(w) => w.push(x),
        }
    }
}
