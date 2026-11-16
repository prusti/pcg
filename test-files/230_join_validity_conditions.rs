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

// The `None`-like path lends `x` to the borrow made after `bb0` chose the
// other branch; the lent edge does not carry that choice into this path.
fn lend_without_branch_choice(c: bool, d: bool) {
    // PCG: bb0 -> bb3: Lend x to borrow: _11 before bb1[7]:PreMain <before bb1[4]:PreOperands> = &mut  x
    let mut x = (1, 2);
    let mut z = (3, 4);
    let mut r: &mut (i32, i32) = &mut z;
    if c && {
        r = &mut x;
        d
    } {
        return;
    }
    *r = (0, 0);
}

fn main() {}
