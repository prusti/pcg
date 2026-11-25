// option PCG_ALLOW_BORROWCK_ERRORS: true

// E0384, reported by borrow checking.
fn assign_twice() -> u32 {
    let x = 0;
    x = 1;
    x
}
