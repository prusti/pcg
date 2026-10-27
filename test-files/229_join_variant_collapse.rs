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
    // PCG: bb2 -> bb4: Weaken x@V.0.g from E to W
    // PCG: bb2 -> bb4: Collapse(RepackCollapse { to: (_1@V).0, capability: W, guide: None, _marker: PhantomData<&()> })
    // PCG: bb2 -> bb4: Collapse(RepackCollapse { to: (_1@V), capability: W, guide: None, _marker: PhantomData<&()> })
    // PCG: bb2 -> bb4: Collapse(RepackCollapse { to: _1, capability: W, guide: Some(Downcast(Some("V"), 0)), _marker: PhantomData<&()> })
    // PCG: bb3 -> bb4: Weaken x from E to W
    x = y;
}

// The `None` path did not match `Some`: it lends `x` itself to the borrow of
// the `Some` field instead of unpacking `x` to that variant.
fn lent_variant_field(mut x: Option<i32>) {
    // PCG: bb3 -> bb5: Lend x to borrow: v before bb4[7]:PreMain <before bb4[3]:PreOperands> = &mut  x@Some.0 under conditions bb0 -> bb2
    // ~PCG: bb3 -> bb5: unpack x@Some with capability E
    let r: &mut i32;
    let mut y = 0;
    match x {
        Some(ref mut v) => r = v,
        None => r = &mut y,
    }
    *r = 1;
    x = None;
    let _ = x;
}

fn main() {}
