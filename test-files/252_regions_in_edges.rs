// Edges between `RegionsIn` projections when a value is moved. An edge exists
// only between projections of the same type parameter or the same alias type.

trait Tr<'a> {
    type Assoc;
}

trait Tr2<'a, 'b> {
    type Assoc;
}

trait Plain {
    type Assoc;
}

fn params<T, U>(x: (T, U)) -> (T, U) {
    // PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(T) -> y↓RegionsIn(T)
    // PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(U) -> y↓RegionsIn(U)
    // ~PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(T) -> y↓RegionsIn(U)
    // ~PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(U) -> y↓RegionsIn(T)
    let y = x;
    y
}

fn alias_and_param<T: Plain>(x: (T, <T as Plain>::Assoc)) -> (T, <T as Plain>::Assoc) {
    // PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(T) -> y↓RegionsIn(T)
    // PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(<T as Plain>::Assoc) -> y↓RegionsIn(<T as Plain>::Assoc)
    // ~PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(T) -> y↓RegionsIn(<T as Plain>::Assoc)
    // ~PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(<T as Plain>::Assoc) -> y↓RegionsIn(T)
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
fn aliases_sharing_a_lifetime<'a, T: Tr<'a> + Tr2<'a, 'a>>(
    x: (<T as Tr<'a>>::Assoc, <T as Tr2<'a, 'a>>::Assoc),
) -> (<T as Tr<'a>>::Assoc, <T as Tr2<'a, 'a>>::Assoc) {
    // PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(<T as Tr<'_>>::Assoc) -> y↓RegionsIn(<T as Tr<'_>>::Assoc)
    // PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(<T as Tr2<'_, '_>>::Assoc) -> y↓RegionsIn(<T as Tr2<'_, '_>>::Assoc)
    // ~PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(<T as Tr<'_>>::Assoc) -> y↓RegionsIn(<T as Tr2<'_, '_>>::Assoc)
    // ~PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(<T as Tr2<'_, '_>>::Assoc) -> y↓RegionsIn(<T as Tr<'_>>::Assoc)
    let y = x;
    y
}

// The regions in the alias are renumbered differently for `x` and `y`.
fn same_alias<'a, T: Tr<'a>>(x: <T as Tr<'a>>::Assoc) -> <T as Tr<'a>>::Assoc {
    // PCG: bb0[1] post_main: Add Edge x before bb0[1]:PostOperands↓RegionsIn(<T as Tr<'_>>::Assoc) -> y↓RegionsIn(<T as Tr<'_>>::Assoc)
    let y = x;
    y
}

struct W<'a, T: Tr2<'a, 'a>> {
    f: <T as Tr2<'a, 'a>>::Assoc,
}

// The type of `w.f` contains the same region twice.
fn same_alias_repeated_region<'a, T: Tr2<'a, 'a>>(w: W<'a, T>) -> <T as Tr2<'a, 'a>>::Assoc {
    // PCG: bb0[1] post_main: Add Edge w.f before bb0[1]:PostOperands↓RegionsIn(<T as Tr2<'_, '_>>::Assoc) -> y↓RegionsIn(<T as Tr2<'_, '_>>::Assoc)
    let y = w.f;
    y
}

fn main() {}
