struct Pair {
    first: u32,
    second: u32,
}

// `r` is only written to by the loop and is initialized at its head
// regardless of whether the loop is entered, so it retains E.
fn write_only_in_loop(n: u32) -> u32 {
    let mut i = 0;
    let mut r = 0;
    // PCG: bb1 loop invariant: r: E
    // PCG: bb1[0] pre_operands: r: E
    // PCG: bb2[3] pre_main: Weaken r from E to W
    while {
        r = i;
        i < n
    } {
        i += 1;
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

// `r` is moved out of by the loop, so it is not initialized at the loop head
// after the first iteration.
fn moved_in_loop(mut r: String, run: bool) {
    // PCG: bb0 -> bb1: Weaken(Weaken { place: _1, from: E, to: W, for_storage_dead: false, _marker: PhantomData<&()> })
    // PCG: bb1 loop invariant: r: W
    // PCG: bb1[0] pre_operands: r: W
    while run {
        r = String::new();
        drop(r);
    }
}

fn main() {}
