// option PCG_ALLOW_BORROWCK_ERRORS: true

fn assign_twice() -> u32 {
    let x = 0;
    x = 1;
    x
}

// E0004 in a closure of a function that defines an opaque type: rustc borrow
// checks the function, and the closure with it, when it checks the opaque
// type, before its MIR borrow checking pass.
fn non_exhaustive_in_closure(o: Option<u32>) -> impl Copy {
    let f = |o: Option<u32>| match o {
        Some(x) => x,
    };
    f(o)
}
