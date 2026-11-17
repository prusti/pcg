fn test() {
    let mut x = [13, 37, 72];
    let y: &mut [i32] = &mut x;
    y[1] = 3;
    // PCG: bb1[1] pre_operands: Remove Edge {*y} -> {(*y)[_5]} (guide=Index(_5))
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

/// The same in a loop body.
fn borrow_and_read_fields_of_indexed_element_in_loop(hdrs: [H; 32], n: usize) -> u8 {
    let mut x = 0;
    for i in 0..n {
        x = g(&hdrs[i].a, hdrs[i].b);
    }
    x
}
