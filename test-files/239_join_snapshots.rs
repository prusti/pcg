#![feature(box_patterns)]

struct Node {
    next: Option<Box<Node>>,
}

fn snapshot_before_join_weakening(mut node: Node) {
    // PCG: bb4[4] post_main: x: e
    // PCG: bb4 -> bb5: Weaken(Weaken { place: _2, from: e, to: W, for_storage_dead: false, _marker: PhantomData<&()> })
    // PCG: bb5[0] pre_operands: x: W

    // We use after bb4 instead of before bb5 because Prusti can refer to the version of `x` after bb4:
    // before bb5, the weaken has already occurred and x is inaccessible.
    // PCG: bb5[0] pre_operands: {*x after bb4} -> {(*x).next after bb4} under conditions bb0 -> bb2
    // ~PCG: bb5[0] pre_operands: {*x before join bb5} -> {(*x).next before join bb5} under conditions bb0 -> bb2
    let mut x = &mut node;
    x = match x.next {
        Some(box ref mut next) => next,
        None => x,
    };
    x.next = None;
}

enum Next {
    Left(Box<BranchNode>),
    Right(Box<BranchNode>),
    None,
}

struct BranchNode {
    next: Next,
}

fn snapshots_from_multiple_predecessors(mut node: BranchNode) {
    // Each borrowed arm must retain its own snapshot and branch condition.
    // PCG: bb5[4] post_main: x: e
    // PCG: bb6[4] post_main: x: e
    // PCG: bb5 -> bb7: Weaken(Weaken { place: _2, from: e, to: W, for_storage_dead: false, _marker: PhantomData<&()> })
    // PCG: bb6 -> bb7: Weaken(Weaken { place: _2, from: e, to: W, for_storage_dead: false, _marker: PhantomData<&()> })
    // PCG: bb7[0] pre_operands: x: W
    // PCG: bb7[0] pre_operands: {*x after bb5} -> {(*x).next after bb5} under conditions bb0 -> bb3
    // PCG: bb7[0] pre_operands: {*x after bb6} -> {(*x).next after bb6} under conditions bb0 -> bb2
    let mut x = &mut node;
    x = match x.next {
        Next::Left(box ref mut next) => next,
        Next::Right(box ref mut next) => next,
        Next::None => {
            // Move x through a tuple to prevent an implicit reborrow.
            let moved = (x,);
            moved.0
        }
    };
    x.next = Next::None;
}

fn main() {}
