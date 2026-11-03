// Arguments whose type is an associated type with a lifetime argument. 
// The whole associated type is one opaque `RegionsIn(..)`, so the lifetime 
// inside it must not be introduced as a separate projection of the argument.
trait AssocWithLifetime<'a> {
    type Out;
}

fn assoc<'a, T: AssocWithLifetime<'a>>(x: <T as AssocWithLifetime<'a>>::Out) {
    // PCG: bb0[0] pre_operands: Remove Edge Remote(_1)↓RegionsIn(<T as AssocWithLifetime<'_>>::Out) -> x↓RegionsIn(<T as AssocWithLifetime<'_>>::Out)
    // ~PCG: bb0[0] pre_operands: Remove Edge Remote(_1)↓'?3 -> x↓'?3
}

trait GatWithLifetime {
    type Out<'a>
    where
        Self: 'a;
}

fn gat<'a, T: GatWithLifetime>(x: T::Out<'a>) {
    // PCG: bb0[0] pre_operands: Remove Edge Remote(_1)↓RegionsIn(<T as GatWithLifetime>::Out<'_>) -> x↓RegionsIn(<T as GatWithLifetime>::Out<'_>)
    // ~PCG: bb0[0] pre_operands: Remove Edge Remote(_1)↓'?3 -> x↓'?3
}

fn main() {}
