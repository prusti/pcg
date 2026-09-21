// Successor actions must prepare borrowed-place expansions on initial loop
// entry and on backedges, while reusing expansions that already exist.

struct Pair {
    first: i32,
    second: i32,
}

struct Outer {
    pair: Pair,
}

struct RefPair<'a> {
    first: &'a i32,
    second: i32,
}

fn borrowed_field(pair: &mut Pair, run: bool) {
    // PCG: bb1[0] pre_operands: pair: R
    // PCG: bb0 -> bb1: Add Edge {pair} -> {*pair}
    // PCG: bb0 -> bb1: Add Edge {*pair} -> {(*pair).first, (*pair).second}
    // PCG: bb4 -> bb1: Add Edge {pair} -> {*pair}
    // PCG: bb4 -> bb1: Add Edge {*pair} -> {(*pair).first, (*pair).second}
    while run {
        std::hint::black_box(&pair.first);
    }
}

fn conditional_entry(pair: &mut Pair, enter: bool, run: bool) {
    // The entry actions omit the branch choice being taken. The backedge
    // retains that outer choice, but does not depend on choices inside the loop.
    // PCG: bb1[0] pre_operands: pair: R
    // PCG: bb0 -> bb1: Add Edge {pair} -> {*pair}
    // PCG: bb0 -> bb1: Add Edge {*pair} -> {(*pair).first, (*pair).second}
    // PCG: bb4 -> bb1: Add Edge {pair} -> {*pair} under conditions bb0 -> bb1
    // PCG: bb4 -> bb1: Add Edge {*pair} -> {(*pair).first, (*pair).second} under conditions bb0 -> bb1
    if enter {
        while run {
            std::hint::black_box(&pair.first);
        }
    }
}

fn nested_fields(outer: &mut Outer, run: bool) {
    // PCG: bb1[0] pre_operands: outer: R
    // PCG: bb0 -> bb1: Add Edge {outer} -> {*outer}
    // PCG: bb0 -> bb1: Add Edge {*outer} -> {(*outer).pair}
    // PCG: bb0 -> bb1: Add Edge {(*outer).pair} -> {(*outer).pair.first, (*outer).pair.second}
    // PCG: bb4 -> bb1: Add Edge {outer} -> {*outer}
    // PCG: bb4 -> bb1: Add Edge {*outer} -> {(*outer).pair}
    // PCG: bb4 -> bb1: Add Edge {(*outer).pair} -> {(*outer).pair.first, (*outer).pair.second}
    while run {
        std::hint::black_box(&outer.pair.first);
    }
}

fn existing_expansions(pair: &mut Pair, run: bool) {
    // PCG: bb1[0] pre_operands: pair: R
    // PCG: bb1[0] pre_operands: {pair} -> {*pair}
    // PCG: bb1[0] pre_operands: {*pair} -> {(*pair).first, (*pair).second}
    // ~PCG: bb0 -> bb1: Add Edge {pair} -> {*pair}
    // ~PCG: bb0 -> bb1: Add Edge {*pair} -> {(*pair).first, (*pair).second}
    // ~PCG: bb5 -> bb1: Add Edge {pair} -> {*pair}
    // ~PCG: bb5 -> bb1: Add Edge {*pair} -> {(*pair).first, (*pair).second}
    // ~PCG: bb5 -> bb1: Add Edge {pair} -> {*pair} under conditions bb2 -> bb3
    // ~PCG: bb5 -> bb1: Add Edge {*pair} -> {(*pair).first, (*pair).second} under conditions bb2 -> bb3
    let hold = &pair.first;
    while run {
        std::hint::black_box(hold);
        std::hint::black_box(&pair.first);
    }
}

fn reference_field(pair: &RefPair<'_>, run: bool) {
    // PCG_LIFETIME_DISPLAY: pair 0 'pair
    // PCG_LIFETIME_DISPLAY: pair 1 'first
    // PCG: bb1[0] pre_operands: pair: R
    // PCG: bb0 -> bb1: Add Edge {pair} -> {*pair}
    // PCG: bb0 -> bb1: Add Edge {pair↓'first loop bb1} -> {*pair↓'first}
    // PCG: bb0 -> bb1: Label lifetime projection pair↓'first with label loop bb1
    // PCG: bb0 -> bb1: Add Edge {*pair} -> {(*pair).first, (*pair).second}
    // PCG: bb0 -> bb1: Add Edge {*pair↓'first} -> {(*pair).first↓'first}
    // PCG: bb0 -> bb1: Add Edge {(*pair).first} -> {*(*pair).first}
    // PCG: bb4 -> bb1: Add Edge {pair} -> {*pair}
    // PCG: bb4 -> bb1: Add Edge {pair↓'first loop bb1} -> {*pair↓'first}
    // PCG: bb4 -> bb1: Label lifetime projection pair↓'first with label loop bb1
    // PCG: bb4 -> bb1: Add Edge {*pair} -> {(*pair).first, (*pair).second}
    // PCG: bb4 -> bb1: Add Edge {*pair↓'first} -> {(*pair).first↓'first}
    // PCG: bb4 -> bb1: Add Edge {(*pair).first} -> {*(*pair).first}
    while run {
        std::hint::black_box(&*pair.first);
    }
}

fn main() {}
