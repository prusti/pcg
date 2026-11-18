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
