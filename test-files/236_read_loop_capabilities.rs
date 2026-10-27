struct Pair {
    first: i32,
    second: i32,
}

fn mixed_fields(mut pair: Pair, run: bool) -> i32 {
    // PCG: bb1[0] pre_operands: pair.first: E
    // PCG: bb1[0] pre_operands: pair.second: R
    // PCG: bb3[0] pre_operands: pair.first: E
    // PCG: bb3[0] pre_operands: pair.second: R
    while run {
        pair.first = pair.second;
        std::hint::black_box(&pair.second);
    }
    pair.first
}

fn read_aggregate(pair: Pair, run: bool) -> Pair {
    // PCG: bb1[0] pre_operands: pair: R
    // PCG: bb4[0] pre_operands: pair: R
    // PCG: bb6[0] pre_operands: pair: E
    while run {
        std::hint::black_box(&pair);
        std::hint::black_box(pair.first);
    }
    pair
}

fn read_borrowed_field(pair: &mut Pair, run: bool) {
    // PCG: bb1[0] pre_operands: pair: R
    // PCG: bb2[0] pre_operands: pair: R
    // PCG: bb3[0] pre_operands: pair: R
    while run {
        std::hint::black_box(&pair.first);
    }
    pair.first = 3;
}

fn nested(mut value: i32, outer: bool, inner: bool) -> i32 {
    // PCG: bb1[0] pre_operands: value: E
    // PCG: bb5[0] pre_operands: value: R
    // PCG: bb7[0] pre_operands: value: R
    // PCG: bb9[0] pre_operands: value: E
    while outer {
        value += 1;
        while inner {
            std::hint::black_box(&value);
        }
        value += 1;
    }
    value
}

struct Stack {
    entries: Vec<u32>,
    depth: usize,
}

fn same(a: &u32, b: &u32) -> Result<bool, ()> {
    Ok(a == b)
}

impl Stack {
    // Lending the referent `*self` to the loop leaves what `self` itself
    // suspends unchanged.
    fn check(&self, child: u32) -> Result<(), usize> {
        // PCG: bb4 -> bb5: Lend *self to Loop(bb5): self -> (*self).depth
        // PCG: bb5[0] pre_operands: self: suspended E
        for entry in self.entries.iter().rev() {
            if same(entry, &child).map_err(|_| self.depth)? {
                return Err(self.depth);
            }
        }
        Ok(())
    }
}

fn main() {}
