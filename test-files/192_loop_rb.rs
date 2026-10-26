struct List<T> {
    head: T,
    tail: Node<T>,
}

impl<T> List<T> {
    fn len(&self) -> usize {
        let mut current = self;
        let mut len = 0;
        while let Some(ref next) = &current.tail {
            len += 1;
            current = next;
        }
        len
    }
}

pub type Node<T> = Option<Box<List<T>>>;

fn loop_rb(a_in: &mut List<i32>, b_in: &mut List<i32>) {
    let mut a = &mut *a_in;
    let b = &mut *b_in;
    let mut x = None;
    let mut cont = true;
    // The borrow of `b` survives the loop.
    // PCG: bb1[0] post_main: borrow: b <loop bb1> = &mut  *b_in
    // At the join after the `if`, each branch unpacks the reference the other
    // branch reborrowed from and lends its `tail`, keeping `head`.
    // PCG: bb7 -> bb9: Add Edge {b} -> {*b} under conditions bb2 -> bb3, bb6 -> bb8 setting b: e, *b: E
    // PCG: bb7 -> bb9: Add Edge {*b} -> {(*b).head, (*b).tail} under conditions bb2 -> bb3, bb6 -> bb8 setting *b: None, (*b).head: E, (*b).tail: E
    // PCG: bb7 -> bb9: Lend (*b).tail to borrow: _22 before bb8[10]:PreMain <before bb8[5]:PreOperands> = &mut  (*b).tail under conditions bb2 -> bb3, bb6 -> bb8
    // PCG: bb8 -> bb9: Lend (*a).tail to borrow: _19 before bb7[4]:PostOperands = &mut  (*a).tail under conditions bb2 -> bb3, bb6 -> bb7
    while cont {
        a = a.tail.as_mut().unwrap();
        cont = a.len() > 0;
        if a.head > 0 {
            x = Some(&mut a.tail);
        } else {
            x = Some(&mut b.tail);
        }
    }
    *x.unwrap() = None;
    a_in.tail = None;
}
fn main(){}
