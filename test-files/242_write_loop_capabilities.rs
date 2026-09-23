struct Pair {
    first: u32,
    second: u32,
}

// `r` is only written to by the loop and is dead at its head, so its
// capability is weakened to W on entry to the loop and on the back edge.
fn write_only_in_loop(n: u32) -> u32 {
    let mut i = 0;
    let mut r = 0;
    // PCG: bb0 -> bb1: Weaken(Weaken { place: _3, from: E, to: W, for_storage_dead: false, _marker: PhantomData<&()> })
    // PCG: bb1 loop invariant: r: W
    // PCG: bb1[0] pre_operands: r: W
    // PCG: bb4 -> bb1: Weaken(Weaken { place: _3, from: E, to: W, for_storage_dead: false, _marker: PhantomData<&()> })
    // ~PCG: bb2[3] pre_main: Weaken r from E to W
    while {
        r = i;
        i < n
    } {
        i += 1;
    }
    r
}

// `r` is only written to by the loop but its value at the head is read after
// the loop exits, so it retains E.
fn write_only_live_at_head(mut r: u32, run: bool) -> u32 {
    // PCG: bb1 loop invariant: r: E
    // PCG: bb1[0] pre_operands: r: E
    // PCG: bb4[0] pre_operands: r: E
    while run {
        r = 1;
    }
    r
}

fn write_only_field(mut pair: Pair, run: bool) -> Pair {
    // PCG: bb1 loop invariant: pair.first: E
    // PCG: bb1 loop invariant: pair.second: R
    // PCG: bb1[0] pre_operands: pair.first: E
    // PCG: bb1[0] pre_operands: pair.second: R
    while run {
        pair.first = pair.second;
    }
    pair
}

fn main() {}
