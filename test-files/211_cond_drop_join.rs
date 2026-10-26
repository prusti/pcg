struct Pair { fst: String, snd: String }

fn rand_bool() -> bool {
    true
}

fn ex1_replace_fst_cond(mut p: Pair, s: String) -> Pair {
    if rand_bool() {
        drop(p.fst);
    }
    // PCG: bb4 -> bb5: unpack p with capability E
    // PCG: bb4 -> bb5: Weaken p.fst from E to W
    p.fst = s;
    p
}

struct Chars<'ch> {
    chars: &'ch str,
    index: usize,
}

fn halves(chars: &str) -> Option<&str> {
    None
}

// One branch moves `p` while the other keeps it frozen, with `*p.chars`
// reborrowed into the result. The frozen side gives up the value of `p`
// explicitly; the reborrow refers to the labelled referent.
fn moved_or_frozen<'ch>(p: Chars<'ch>) -> Chars<'ch> {
    // PCG: bb5 -> bb6: Label place p (Write)
    // PCG: bb5 -> bb6: Unfreeze p
    // PCG: bb5 -> bb6: Weaken p from E to W
    // PCG: bb6[0] pre_operands: p: W
    // PCG: bb6[0] pre_operands: {p.chars after bb5} -> {*p.chars after bb5} under conditions bb1 -> bb3
    match halves(p.chars) {
        Some(left) => Chars { chars: left, index: 0 },
        None => p,
    }
}

struct Occupied<'a> {
    table: &'a mut Vec<u32>,
    hash_builder: &'a String,
}

struct Vacant<'a> {
    table: &'a mut Vec<u32>,
    hash_builder: &'a String,
}

enum Entry<'a> {
    Occupied(Occupied<'a>),
    Vacant(Vacant<'a>),
}

// As above, but the other branch moves the parent `o` as a whole.
fn moved_parent_or_frozen(o: Occupied<'_>, b: bool) -> Entry<'_> {
    // PCG: bb2 -> bb3: Label place o.hash_builder (Write)
    // PCG: bb2 -> bb3: Unfreeze o.hash_builder
    // PCG: bb2 -> bb3: Weaken o.hash_builder from E to W
    // PCG: bb3[0] pre_operands: o: W
    // PCG: bb3[0] pre_operands: {o.hash_builder after bb2} -> {*o.hash_builder after bb2} under conditions bb0 -> bb2
    if b {
        Entry::Occupied(o)
    } else {
        Entry::Vacant(Vacant {
            table: o.table,
            hash_builder: o.hash_builder,
        })
    }
}
