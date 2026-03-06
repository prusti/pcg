fn bar() -> *mut i32 {
    let mut x = 5;
    &raw mut x
    // Before the storagedead, there should be a weaken from D to U
    // PCG: bb0[4] pre_main: Weaken x from D to U
    // PCG: bb0[4] pre_main: Label place x (Write)
}
