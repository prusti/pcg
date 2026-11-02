// Arguments whose type is an associated type with a lifetime argument. The
// whole associated type is one opaque `RegionsIn(..)`, so the lifetime inside
// it must not be introduced as a separate projection of the argument.
trait Tr<'a> {
    type Out;
}

fn assoc<'a, T: Tr<'a>>(x: <T as Tr<'a>>::Out) {}

trait Lending {
    type Item<'a>
    where
        Self: 'a;
}

fn gat<'a, T: Lending>(x: T::Item<'a>) {}

fn main() {}
