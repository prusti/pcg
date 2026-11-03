// Edges between `RegionsIn` projections when a value is moved, borrowed or
// assigned. An edge exists only between projections of the same type parameter
// or the same alias type.

trait AssocWithLifetime<'a> {
    type Out;
}

trait AssocWithTwoLifetimes<'a, 'b> {
    type Out;
}

trait AssocWithoutLifetime {
    type Out;
}

fn params<T, U>(x: (T, U)) -> (T, U) {
    // PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(T) -> y↓RegionsIn(T)
    // PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(U) -> y↓RegionsIn(U)
    // ~PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(T) -> y↓RegionsIn(U)
    // ~PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(U) -> y↓RegionsIn(T)
    let y = x;
    y
}

fn borrow_pair<T, U>(mut x: (T, U)) -> (T, U) {
    // PCG: bb0[1] post_main: Add Edge x↓RegionsIn(T) before bb0[1]:PostMain -> r↓RegionsIn(T)
    // PCG: bb0[1] post_main: Add Edge x↓RegionsIn(U) before bb0[1]:PostMain -> r↓RegionsIn(U)
    // ~PCG: bb0[1] post_main: Add Edge x↓RegionsIn(T) before bb0[1]:PostMain -> r↓RegionsIn(U)
    // ~PCG: bb0[1] post_main: Add Edge x↓RegionsIn(U) before bb0[1]:PostMain -> r↓RegionsIn(T)
    // ~PCG: bb0[1] post_main: Add Edge r↓RegionsIn(T) -> x↓RegionsIn(U) FUTURE
    // ~PCG: bb0[1] post_main: Add Edge r↓RegionsIn(U) -> x↓RegionsIn(T) FUTURE
    let r = &mut x;
    let _ = r;
    x
}

fn assign_pair<T, U>(x: &mut (T, U), y: (T, U)) {
    // PCG: bb0[1] post_main: Add Edge y before bb0[1]:PostOperands↓RegionsIn(T) -> _3↓RegionsIn(T)
    // PCG: bb0[1] post_main: Add Edge y before bb0[1]:PostOperands↓RegionsIn(U) -> _3↓RegionsIn(U)
    // ~PCG: bb0[1] post_main: Add Edge y before bb0[1]:PostOperands↓RegionsIn(T) -> _3↓RegionsIn(U)
    // ~PCG: bb0[1] post_main: Add Edge y before bb0[1]:PostOperands↓RegionsIn(U) -> _3↓RegionsIn(T)
    *x = y;
}

fn alias_and_param<T: AssocWithoutLifetime>(x: (T, <T as AssocWithoutLifetime>::Out)) -> (T, <T as AssocWithoutLifetime>::Out) {
    // PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(T) -> y↓RegionsIn(T)
    // PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(<T as AssocWithoutLifetime>::Out) -> y↓RegionsIn(<T as AssocWithoutLifetime>::Out)
    // ~PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(T) -> y↓RegionsIn(<T as AssocWithoutLifetime>::Out)
    // ~PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(<T as AssocWithoutLifetime>::Out) -> y↓RegionsIn(T)
    let y = x;
    y
}

fn different_aliases<I: Iterator, J: Iterator>(x: (I::Item, J::Item)) -> (I::Item, J::Item) {
    // PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(<I as std::iter::Iterator>::Item) -> y↓RegionsIn(<I as std::iter::Iterator>::Item)
    // PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(<J as std::iter::Iterator>::Item) -> y↓RegionsIn(<J as std::iter::Iterator>::Item)
    // ~PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(<I as std::iter::Iterator>::Item) -> y↓RegionsIn(<J as std::iter::Iterator>::Item)
    // ~PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(<J as std::iter::Iterator>::Item) -> y↓RegionsIn(<I as std::iter::Iterator>::Item)
    let y = x;
    y
}

// Both aliases mention `'a`, but they are still different types.
fn aliases_sharing_a_lifetime<'a, T: AssocWithLifetime<'a> + AssocWithTwoLifetimes<'a, 'a>>(
    x: (<T as AssocWithLifetime<'a>>::Out, <T as AssocWithTwoLifetimes<'a, 'a>>::Out),
) -> (<T as AssocWithLifetime<'a>>::Out, <T as AssocWithTwoLifetimes<'a, 'a>>::Out) {
    // PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(<T as AssocWithLifetime<'_>>::Out) -> y↓RegionsIn(<T as AssocWithLifetime<'_>>::Out)
    // PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(<T as AssocWithTwoLifetimes<'_, '_>>::Out) -> y↓RegionsIn(<T as AssocWithTwoLifetimes<'_, '_>>::Out)
    // ~PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(<T as AssocWithLifetime<'_>>::Out) -> y↓RegionsIn(<T as AssocWithTwoLifetimes<'_, '_>>::Out)
    // ~PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(<T as AssocWithTwoLifetimes<'_, '_>>::Out) -> y↓RegionsIn(<T as AssocWithLifetime<'_>>::Out)
    let y = x;
    y
}

// The regions in the alias are renumbered differently for `x` and `y`.
fn same_alias<'a, T: AssocWithLifetime<'a>>(x: <T as AssocWithLifetime<'a>>::Out) -> <T as AssocWithLifetime<'a>>::Out {
    // PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(<T as AssocWithLifetime<'_>>::Out) -> y↓RegionsIn(<T as AssocWithLifetime<'_>>::Out)
    let y = x;
    y
}

struct W<'a, T: AssocWithTwoLifetimes<'a, 'a>> {
    f: <T as AssocWithTwoLifetimes<'a, 'a>>::Out,
}

// The type of `w.f` contains the same region twice.
fn same_alias_repeated_region<'a, T: AssocWithTwoLifetimes<'a, 'a>>(w: W<'a, T>) -> <T as AssocWithTwoLifetimes<'a, 'a>>::Out {
    // PCG: bb0[1] post_main: Add Edge w.f before bb0[1]:PostOperands↓RegionsIn(<T as AssocWithTwoLifetimes<'_, '_>>::Out) -> y↓RegionsIn(<T as AssocWithTwoLifetimes<'_, '_>>::Out)
    let y = w.f;
    y
}

fn main() {}
