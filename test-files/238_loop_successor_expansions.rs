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
    // PCG: bb0 -> bb1: Add Edge {pair} -> {*pair} setting pair: R, *pair: R
    // PCG: bb0 -> bb1: Add Edge {*pair} -> {(*pair).first, (*pair).second} setting *pair: R, (*pair).first: R, (*pair).second: R
    // PCG: bb4 -> bb1: Add Edge {pair} -> {*pair} setting pair: R, *pair: R
    // PCG: bb4 -> bb1: Add Edge {*pair} -> {(*pair).first, (*pair).second} setting *pair: R, (*pair).first: R, (*pair).second: R
    while run {
        std::hint::black_box(&pair.first);
    }
}

fn conditional_entry(pair: &mut Pair, enter: bool, run: bool) {
    // The entry actions omit the branch choice being taken. The backedge
    // retains that outer choice, but does not depend on choices inside the loop.
    // PCG: bb1[0] pre_operands: pair: R
    // PCG: bb0 -> bb1: Add Edge {pair} -> {*pair} setting pair: R, *pair: R
    // PCG: bb0 -> bb1: Add Edge {*pair} -> {(*pair).first, (*pair).second} setting *pair: R, (*pair).first: R, (*pair).second: R
    // PCG: bb4 -> bb1: Add Edge {pair} -> {*pair} under conditions bb0 -> bb1 setting pair: R, *pair: R
    // PCG: bb4 -> bb1: Add Edge {*pair} -> {(*pair).first, (*pair).second} under conditions bb0 -> bb1 setting *pair: R, (*pair).first: R, (*pair).second: R
    // Borrow edges created inside the loop retain the outer branch choice.
    // PCG: bb3[2] pre_operands: {pair} -> {*pair} under conditions bb0 -> bb1, bb2 -> bb3
    if enter {
        while run {
            std::hint::black_box(&pair.first);
        }
    }
}

fn nested_fields(outer: &mut Outer, run: bool) {
    // PCG: bb1[0] pre_operands: outer: R
    // PCG: bb0 -> bb1: Add Edge {outer} -> {*outer} setting outer: R, *outer: R
    // PCG: bb0 -> bb1: Add Edge {*outer} -> {(*outer).pair} setting *outer: R, (*outer).pair: R
    // PCG: bb0 -> bb1: Add Edge {(*outer).pair} -> {(*outer).pair.first, (*outer).pair.second} setting (*outer).pair: R, (*outer).pair.first: R, (*outer).pair.second: R
    // PCG: bb4 -> bb1: Add Edge {outer} -> {*outer} setting outer: R, *outer: R
    // PCG: bb4 -> bb1: Add Edge {*outer} -> {(*outer).pair} setting *outer: R, (*outer).pair: R
    // PCG: bb4 -> bb1: Add Edge {(*outer).pair} -> {(*outer).pair.first, (*outer).pair.second} setting (*outer).pair: R, (*outer).pair.first: R, (*outer).pair.second: R
    while run {
        std::hint::black_box(&outer.pair.first);
    }
}

fn existing_expansions(pair: &mut Pair, run: bool) {
    // PCG: bb1[0] pre_operands: pair: R
    // PCG: bb1[0] pre_operands: {pair} -> {*pair}
    // PCG: bb1[0] pre_operands: {*pair} -> {(*pair).first, (*pair).second}
    // ~PCG: bb0 -> bb1: Add Edge {pair} -> {*pair} setting pair: R, *pair: R
    // ~PCG: bb0 -> bb1: Add Edge {*pair} -> {(*pair).first, (*pair).second} setting *pair: R, (*pair).first: R, (*pair).second: R
    // ~PCG: bb5 -> bb1: Add Edge {pair} -> {*pair} setting pair: R, *pair: R
    // ~PCG: bb5 -> bb1: Add Edge {*pair} -> {(*pair).first, (*pair).second} setting *pair: R, (*pair).first: R, (*pair).second: R
    // ~PCG: bb5 -> bb1: Add Edge {pair} -> {*pair} under conditions bb2 -> bb3 setting pair: R, *pair: R
    // ~PCG: bb5 -> bb1: Add Edge {*pair} -> {(*pair).first, (*pair).second} under conditions bb2 -> bb3 setting *pair: R, (*pair).first: R, (*pair).second: R
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
    // PCG: bb0 -> bb1: Add Edge {pair} -> {*pair} setting pair: R, *pair: R
    // PCG: bb0 -> bb1: Add Edge {*pair} -> {(*pair).first, (*pair).second} setting *pair: R, (*pair).first: R, (*pair).second: R
    // PCG: bb0 -> bb1: Add Edge {*pair↓'first} -> {(*pair).first↓'first}
    // PCG: bb0 -> bb1: Add Edge {(*pair).first} -> {*(*pair).first} setting (*pair).first: R, *(*pair).first: R
    // PCG: bb4 -> bb1: Add Edge {pair} -> {*pair} setting pair: R, *pair: R
    // PCG: bb4 -> bb1: Add Edge {*pair} -> {(*pair).first, (*pair).second} setting *pair: R, (*pair).first: R, (*pair).second: R
    // PCG: bb4 -> bb1: Add Edge {*pair↓'first} -> {(*pair).first↓'first}
    // PCG: bb4 -> bb1: Add Edge {(*pair).first} -> {*(*pair).first} setting (*pair).first: R, *(*pair).first: R
    while run {
        std::hint::black_box(&*pair.first);
    }
}

struct File<'data> {
    symbols: &'data [u8],
}

struct Iter<'data, 'file> {
    file: &'file File<'data>,
    index: usize,
}

struct Comdat<'data, 'file> {
    file: &'file File<'data>,
    symbol: &'data u8,
}

fn parse<'data, 'file>(
    file: &'file File<'data>,
    symbol: &'data u8,
) -> Option<Comdat<'data, 'file>> {
    if *symbol > 0 {
        Some(Comdat { file, symbol })
    } else {
        None
    }
}

impl<'data, 'file> Iter<'data, 'file> {
    // The back edge unpacks `(*self).file` with the loop's snapshot, which
    // labels its current lifetime projection as the loop's: the flow from the
    // loop's value into it collapses.
    fn next(&mut self) -> Option<Comdat<'data, 'file>> {
        loop {
            let index = self.index;
            let symbol = self.file.symbols.get(index)?;
            self.index += 1;
            if let Some(comdat) = parse(self.file, symbol) {
                return Some(comdat);
            }
        }
    }
}

fn main() {}
