struct A(u32);
struct B {
    f: A,
    g: A,
}
enum E {
    V(B),
    N,
}

// A join of a path that partially moved out of an enum variant with a path
// that left the local packed must announce, on the deep path's edge, the
// weakens of the still-exclusive leaves and the collapse chain back up to
// the local; the local stays live so nothing collapses it earlier.
fn repro(mut x: E, y: E) {
    if let E::V(B { f: z, .. }) = x {}
    // PCG: bb2 -> bb4: Weaken(Weaken { place: (_1@V).0.1, from: E, to: W, for_storage_dead: false, _marker: PhantomData<&()> })
    // PCG: bb2 -> bb4: Collapse(RepackCollapse { to: (_1@V).0, capability: W, guide: None, _marker: PhantomData<&()> })
    // PCG: bb2 -> bb4: Collapse(RepackCollapse { to: (_1@V), capability: W, guide: None, _marker: PhantomData<&()> })
    // PCG: bb2 -> bb4: Collapse(RepackCollapse { to: _1, capability: W, guide: Some(Downcast(Some("V"), 0)), _marker: PhantomData<&()> })
    // PCG: bb3 -> bb4: Weaken(Weaken { place: _1, from: E, to: W, for_storage_dead: false, _marker: PhantomData<&()> })
    x = y;
}

fn main() {}
