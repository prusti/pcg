// PCG_EXPECTED_FAILURE: frame try_reserve
// PCG_EXPECTED_FAILURE: frame try_reserve::{closure#0}
// Reading through `m: &mut M` before a loop must keep the deref chain to
// `*(*m).shards` when the loop abstraction is rooted at `m`'s remote borrow.
// ~PCG: bb6[0] pre_operands: m: E
struct M {
    shards: Box<[std::cell::RefCell<Vec<i32>>]>,
    h: i32,
}

fn try_reserve(m: &mut M) -> Result<(), ()> {
    for s in m.shards.iter() {
        s.borrow_mut().retain(|k| *k == m.h);
    }
    Ok(())
}

fn main() {}
