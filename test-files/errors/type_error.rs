// option PCG_ALLOW_BORROWCK_ERRORS: true

fn assign_twice() -> u32 {
    let x = 0;
    x = 1;
    x
}

// E0308, reported by type checking before any borrow checking.
fn mismatched() -> u32 {
    "not a u32"
}
