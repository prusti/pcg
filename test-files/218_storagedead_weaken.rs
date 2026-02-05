fn bar() -> *mut i32 {
    let mut x = 5;
    &raw mut x
    // Before the storagedead, there should be a weaken from E to W
    // PCG: bb0[4] pre_main: Weaken(Weaken { place: _1, from: E, to: W, _marker: PhantomData<&()> })
    // PCG: bb0[4] pre_main: Label place x (StorageDead)
}
