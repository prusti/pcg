struct List {
    head: i32,
    tail: Option<Box<List>>,
}

fn foo<'a: 'a>(list: &'a mut List) {
    let mut c = &mut list.tail;
    // `list` is dead at the loop head: the loop abstracts its referent as of
    // the head and `list` is only writable.
    // PCG: bb1[0] pre_operands: Loop(bb1): (*list).tail loop bb1 -> c↓'?8
    // PCG: bb1[0] post_operands: list: W
    while let Some(c_tail) = c {
        c = &mut c_tail.tail;
    }
}

fn main(){}
