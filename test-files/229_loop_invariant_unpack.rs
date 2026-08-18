struct Pair {
    fst: String,
    snd: String,
}

// The loop invariant requires full capability to `pair.fst`, so the PCG unpacks
// `pair` at the loop head (bb2) and keeps it unpacked for the whole loop body,
// rather than holding `pair: E` at the head and unpacking inside the loop.
fn write_field_in_loop(mut pair: Pair) {
    let mut cond = false;
    let fst_len = pair.fst.len();
    // PCG: bb2[0] pre_operands: pair.fst: E
    // PCG: bb2[0] pre_operands: pair.snd: E
    // ~PCG: bb2[0] pre_operands: pair: E
    // PCG: bb5[0] post_main: pair.fst: E
    // PCG: bb5[0] post_main: pair.snd: E
    // ~PCG: bb5[0] post_main: pair: E
    while !cond {
        pair.fst = String::new();
        cond = true;
    }
    assert!(fst_len == pair.fst.len())
}

// A field that is only read in the loop is unpacked for `Read`, while the field
// that is written to keeps exclusive capability.
fn read_and_write_fields_in_loop(mut pair: Pair, other: &Pair) {
    let mut cond = false;
    while !cond {
        pair.fst = other.snd.clone();
        cond = pair.snd.is_empty();
    }
}

fn main() {}
