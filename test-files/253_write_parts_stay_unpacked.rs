// Parts of a place that hold only write capability stay unpacked, so that a
// part can be given a value again without unpacking the place at write
// capability. A join packs them where another path holds the whole place
// without a value, or shares it, provided no part is lent out.

struct T1 {
    f: u32,
    g: u32,
}

struct P {
    a: T1,
    b: T1,
}

fn consume(_p: P) {}

fn reinit_after_moving_all_parts(mut x: P, y: T1) {
    // ~PCG: bb0[8] pre_main: unpack x with capability W
    let _a = x.a;
    let _b = x.b;
    x.a = y;
}

fn reinit_box_after_move(mut b: Box<T1>) {
    // ~PCG: bb0[5] pre_main: unpack b with capability W
    let _v = *b;
    *b = T1 { f: 1, g: 2 };
}

fn join_moved_whole_with_moved_parts(c: bool, x: P) {
    // PCG: bb3 -> bb4: Collapse(RepackCollapse { to: _2, capability: W, guide: None, _marker: PhantomData<&()> })
    if c {
        consume(x);
    } else {
        let _a = x.a;
        let _b = x.b;
    }
}

fn join_shared_with_moved_parts(c: bool, x: P, o: &P) {
    // PCG: bb1 -> bb3: Restore capability E to x
    // PCG: bb2 -> bb3: Collapse(RepackCollapse { to: _2, capability: W, guide: None, _marker: PhantomData<&()> })
    let r: &P;
    if c {
        r = &x;
    } else {
        let _a = x.a;
        let _b = x.b;
        r = o;
    }
    let _ = r;
}

struct R<'a> {
    r: &'a mut u32,
    g: T1,
}

fn join_moved_whole_with_lent_part(c: bool, x: R<'_>, o: &mut u32) {
    // `x.r` is lent out, so the moving path unpacks `x` instead.
    // PCG: bb1 -> bb3: unpack x with capability W
    // ~PCG: bb2 -> bb3: Collapse(RepackCollapse { to: _2, capability: W, guide: None, _marker: PhantomData<&()> })
    let p: &mut u32;
    if c {
        let _x = x;
        p = o;
    } else {
        p = &mut *x.r;
        let _g = x.g;
    }
    *p += 1;
}

fn main() {}
