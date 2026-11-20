fn test() {
    let mut x = [13, 37, 72];
    let y: &mut [i32] = &mut x;
    y[1] = 3;
    // PCG: bb1[1] pre_operands: Remove Edge {*y} -> {(*y)[_5]} (guide=Index(_5)) under conditions bb0 -> bb1
}

struct H {
    a: u8,
    b: u32,
}

fn g(_a: &u8, b: u32) -> u8 {
    b as u8
}

/// Each indexing gets its own index temporary, so `hdrs` has two index
/// expansions: to `hdrs[_5]` for the borrow of `.a` and to `hdrs[_8]` for the
/// read of `.b`. Collapsing `hdrs[_8]` before the call must not make `hdrs`
/// collapsible, because `hdrs[_5].a` is lent until the call returns.
fn borrow_and_read_fields_of_indexed_element(hdrs: [H; 32], i: usize) -> u8 {
    g(&hdrs[i].a, hdrs[i].b)
    // PCG: bb2[1] pre_operands: Collapse(RepackCollapse { to: _1[_8], capability: R, guide: None, _marker: PhantomData<&()> })
    // PCG: bb2[1] post_operands: hdrs: R
    // PCG: bb3[0] pre_operands: Collapse(RepackCollapse { to: _1, capability: R, guide: Some(Index(_5)), _marker: PhantomData<&()> })
    // PCG: bb3[0] pre_operands: Collapse(RepackCollapse { to: _1, capability: R, guide: Some(Index(_8)), _marker: PhantomData<&()> })
}

struct S {
    arr: [H; 32],
    z: u8,
}

/// The same for an array in a field. Each of the two collapses of `s.arr`
/// removes only the expansion of its own guide.
fn borrow_and_read_fields_of_indexed_element_of_field(s: S, i: usize) -> u8 {
    g(&s.arr[i].a, s.arr[i].b)
    // PCG: bb3[0] pre_operands: Collapse(RepackCollapse { to: _1.0, capability: R, guide: Some(Index(_8)), _marker: PhantomData<&()> })
    // PCG: bb3[0] pre_operands: Collapse(RepackCollapse { to: _1.0, capability: R, guide: Some(Index(_5)), _marker: PhantomData<&()> })
    // PCG: bb3[0] post_operands: s: E
}

/// The same in a loop body. `hdrs` is only read in the loop, so it keeps R
/// after its expansions are collapsed.
fn borrow_and_read_fields_of_indexed_element_in_loop(hdrs: [H; 32], n: usize) -> u8 {
    let mut x = 0;
    for i in 0..n {
        x = g(&hdrs[i].a, hdrs[i].b);
        // PCG: bb11[0] pre_operands: Collapse(RepackCollapse { to: _1, capability: R, guide: Some(Index(_23)), _marker: PhantomData<&()> })
        // PCG: bb11[0] post_operands: hdrs: R
    }
    x
}

enum E {
    A([String; 2]),
    B,
}

/// The pattern `[x, _]` expands `e.0` into both of its elements under one
/// guide, that of the bound element (offset 0), so the join collapses it once
/// and emits no collapse with an offset-1 guide.
fn join_collapses_constant_index_expansion_once(e: E, c: bool) {
    match e {
        E::A([x, _]) if c => drop(x),
        _ => {}
    }
    // PCG: bb7 -> bb8: Collapse(RepackCollapse { to: (_1@A).0, capability: W, guide: Some(ConstantIndex(ConstantIndex { offset: 0, min_length: 2, from_end: false })), _marker: PhantomData<&()> })
    // ~PCG: bb7 -> bb8: Collapse(RepackCollapse { to: (_1@A).0, capability: W, guide: Some(ConstantIndex(ConstantIndex { offset: 1, min_length: 2, from_end: false })), _marker: PhantomData<&()> })
}

/// Each branch expands `a` for read with a constant-index guide of its own
/// offset, so after the join `a` has two expansions with the same children.
/// Collapsing one of them leaves the children to the other.
fn join_two_constant_index_read_expansions(a: [String; 2], c: bool) -> usize {
    let r = if c {
        let [ref x, _] = a;
        x
    } else {
        let [_, ref y] = a;
        y
    };
    r.len()
    // PCG: bb4[0] pre_operands: Collapse(RepackCollapse { to: _1, capability: R, guide: Some(ConstantIndex(ConstantIndex { offset: 0, min_length: 2, from_end: false })), _marker: PhantomData<&()> })
    // PCG: bb4[0] pre_operands: Collapse(RepackCollapse { to: _1, capability: R, guide: Some(ConstantIndex(ConstantIndex { offset: 1, min_length: 2, from_end: false })), _marker: PhantomData<&()> })
    // PCG: bb4[0] post_operands: a: E
}
