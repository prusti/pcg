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
// Here `'a` is universal, so it outlives the local region of `y`. The alias is
// one `RegionsIn(..)`, so `'a` (`'?4`) gets no projection of its own.
fn alias_tuple_move_local<'a, T: AssocWithLifetime<'a>>(
    x: (<T as AssocWithLifetime<'a>>::Out, &u32),
) {
    // PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(<T as AssocWithLifetime<'_>>::Out) -> y↓'?7
    // ~PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓'?4 -> y↓'?7
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

trait Lend {
    type Out<'y>;
    fn lend<'y>(&self, y: &'y u32) -> Self::Out<'y>;
}

// The borrow of `y` is in the part of the alias's value that its argument
// `'y` names. Moving the value moves that part into the same part of `b`,
// whose region argument is another region variable.
fn move_alias_part<'y, M: Lend>(m: &M, y: &'y u32) -> M::Out<'y> {
    let a = m.lend(y);
    // PCG: bb1[4] post_main: Add Edge a before bb1[4]:PostOperands↓<M as Lend>::Out<'_>[RegionVid('?9)] -> b↓<M as Lend>::Out<'_>[RegionVid('?12)]
    let b = a;
    b
}

trait Iterable<'a> {
    type Out: IntoIterator;
}

// The value of `a` has a part for `RegionsIn` of the alias argument `Q` of
// its type, and one for the `'a` of the where clause on `T`, which `Q`'s own
// region argument equals. Moving the value moves each part into the same part
// of `b`, and the part for `'a` into the part for that region too.
fn move_alias_argument_part<'a, T: Iterable<'a>>(
    q: <T as Iterable<'a>>::Out,
) -> <<T as Iterable<'a>>::Out as IntoIterator>::IntoIter {
    let a = q.into_iter();
    // PCG: bb1[3] post_main: Add Edge a before bb1[3]:PostOperands↓<<T as Iterable<'_>>::Out as std::iter::IntoIterator>::IntoIter[RegionsIn(<T as Iterable<'_>>::Out)] -> b↓<<T as Iterable<'_>>::Out as std::iter::IntoIterator>::IntoIter[RegionsIn(<T as Iterable<'_>>::Out)]
    // PCG: bb1[3] post_main: Add Edge a before bb1[3]:PostOperands↓<<T as Iterable<'_>>::Out as std::iter::IntoIterator>::IntoIter[RegionVid('?1)] -> b↓<<T as Iterable<'_>>::Out as std::iter::IntoIterator>::IntoIter[RegionVid('?1)]
    // PCG: bb1[3] post_main: Add Edge a before bb1[3]:PostOperands↓<<T as Iterable<'_>>::Out as std::iter::IntoIterator>::IntoIter[RegionVid('?6)] -> b↓<<T as Iterable<'_>>::Out as std::iter::IntoIterator>::IntoIter[RegionVid('?1)]
    let b = a;
    b
}

// A part of an alias's value named by a region relates to other regions as
// that region does: as between the regions of two references, the flows of
// an aggregate follow the outlives relation, not the positions.
fn lend_with_ref<'y, M: Lend>(m: &M, y: &'y u32) -> (&'y u32, M::Out<'y>) {
    // PCG: bb1[2] post_main: Add Edge _4 before bb1[2]:PostOperands↓'?12 -> p↓<M as Lend>::Out<'_>[RegionVid('?11)]
    // PCG: bb1[2] post_main: Add Edge _5 before bb1[2]:PostOperands↓<M as Lend>::Out<'_>[RegionVid('?13)] -> p↓'?10
    let p = (y, m.lend(y));
    p
}

trait Named<'a> {}

// A part named by `'static` holds no loans that the PCG tracks, so `I` has
// no part for the `'static` of its bound.
fn static_bound<I: Named<'static>>(x: I) -> I {
    x
}

trait StaticOut {
    type Out: 'static;
    fn write(self, buf: &mut Self::Out) -> &str;
}

// `Out: 'static` means that the value of `I::Out` holds no loans of `I`, so
// the value of `i` does not flow into the result through `buf`.
fn format_into_static_alias<'a, I: StaticOut>(i: I) -> &'a str {
    let p: *mut I::Out = std::ptr::null_mut();
    i.write(unsafe { &mut *p })
}

fn keep_static<V: 'static>(v: V) -> V {
    v
}

// The value of `U::Out` outlives `'static` by the bound of its definition, as
// in the spec of `keep_static`.
fn pass_static_alias<U: StaticOut>(a: U::Out) -> U::Out {
    keep_static(a)
}

trait IterOf<V> {
    type It;
    fn it(self) -> Self::It;
}

// The opaque result's hidden type is an alias with the same arguments in
// another order: their parts pair by the type they are named after.
fn iter_opaque<V, S: IterOf<V>>(s: S) -> impl Sized {
    s.it()
}

fn main() {}
