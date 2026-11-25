// option PCG_ALLOW_BORROWCK_ERRORS: true

fn assign_twice() -> u32 {
    let x = 0;
    x = 1;
    x
}

// E0004 in a function that defines an opaque type: rustc borrow checks it
// when it checks the opaque type, before its MIR borrow checking pass.
fn non_exhaustive(o: Option<u32>) -> impl Copy {
    match o {
        Some(x) => x,
    }
}
