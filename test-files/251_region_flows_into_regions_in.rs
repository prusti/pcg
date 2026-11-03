// Edges between a region and `RegionsIn(T)`. 
// A region outlives `RegionsIn(T)` only if it outlives `'static`.
// `RegionsIn(T)` outlives a region if the region is local.

fn tuple_move_static<T>(x: (T, &'static u32)) -> (T, &'static u32) {
    // PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓'?3 -> y↓RegionsIn(T)
    // ~PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(T) -> y↓'?4
    let y = x;
    y
}

fn tuple_move<'a, T>(x: (T, &'a u32)) -> (T, &'a u32) {
    // ~PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓'?4 -> y↓RegionsIn(T)
    // ~PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(T) -> y↓'?5
    let y = x;
    y
}

fn tuple_move_local<T>(x: (T, &u32)) {
    // PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(T) -> y↓'?4
    let y = x;
    let _ = y;
}

trait AssocWithLifetime<'a> {
    type Out;
}

// For an alias, the regions in its arguments must also outlive the region.
// Here `'a` is universal, so it outlives the local region of `y`.
fn alias_tuple_move_local<'a, T: AssocWithLifetime<'a>>(
    x: (<T as AssocWithLifetime<'a>>::Out, &u32),
) {
    // PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(<T as AssocWithLifetime<'_>>::Out) -> y↓'?7
    let y = x;
    let _ = y;
}

fn make<'x, T: for<'y> AssocWithLifetime<'y, Out: Copy>>(
    _r: &'x u32,
) -> <T as AssocWithLifetime<'x>>::Out {
    unimplemented!()
}

// The alias contains the local borrow of `n`, which is dead once `y` is. The
// reference in `y` lives longer, until `*r` is read, so the alias does not
// outlive it. `Out: Copy` keeps the alias value from being dropped at the end
// of the scope, which would keep its region alive.
fn alias_region_shorter<T: for<'y> AssocWithLifetime<'y, Out: Copy>>(k: &u32) {
    let n = 5;
    // PCG: bb1[3] post_main: Add Edge _7 before bb1[3]:PostOperands↓'?12 -> y↓'?8
    // ~PCG: bb1[3] post_main: Add Edge _4 before bb1[3]:PostOperands↓RegionsIn(<T as AssocWithLifetime<'_>>::Out) -> y↓'?8
    let y = (make::<T>(&n), k);
    let r = y.1;
    let _ = *r;
}

fn main() {}
