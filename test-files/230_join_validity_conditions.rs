//! Regression test: joining validity conditions is a disjunction, so a block
//! whose branches are constrained on one incoming path but unconstrained on
//! the other must be unconstrained in the join.
#![feature(box_patterns)]

struct List {
    value: u32,
    next: Option<Box<List>>,
}

fn from_nth(r: &mut List, n: usize) -> &mut List {
    // bb9 joins the `then` path (bb0 -> bb1) with the `else` path (bb0 -> bb2,
    // bb2 -> bb5, ...). The `then` path says nothing about bb2's branches, so
    // the expansions performed at bb9 are not conditional on bb2 -> bb5.
    // PCG: bb9[0] pre_operands: Add Edge {_4} -> {(*_4)} setting _4: e, (*_4): E
    // PCG: bb9[2] pre_operands: Add Edge {_3} -> {(*_3)} setting _3: e, (*_3): E
    // ~PCG: bb9[0] pre_operands: Add Edge {_4} -> {(*_4)} under conditions bb2 -> bb5 setting _4: e, (*_4): E
    // ~PCG: bb9[2] pre_operands: Add Edge {_3} -> {(*_3)} under conditions bb2 -> bb5 setting _3: e, (*_3): E
    if n == 0 {
        r
    } else {
        match r.next {
            None => unreachable!(),
            Some(box ref mut tail) => from_nth(tail, n - 1),
        }
    }
}

fn main() {}
