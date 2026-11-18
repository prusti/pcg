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

fn read(_r: &i32) {}

// One branch reads through `x` (x: R), the other lends its referent (x: e):
// `x` itself is kept by both, so the join holds it with e.
fn read_or_lent(x: &mut i32, c: bool) {
    // PCG: bb1 -> bb3: Refreeze x to *x
    // PCG: bb3[0] pre_operands: x: e
    // ~PCG: bb2 -> bb3: Weaken x from e to W
    // PCG: bb4[0] pre_operands: x: E
    let r: &i32;
    if c {
        r = &*x;
    } else {
        let m = &mut *x;
        r = &*m;
    }
    read(r);
    *x = 2;
}

// One branch moves `x.fst` out, the other lends `x` as a whole: the first
// collapses `x` to W and lends it, so `x` gets only W back.
fn moved_part_or_lent(c: bool, x0: Pair, mut z: Pair) {
    // PCG: bb2 -> bb4: Collapse(RepackCollapse { to: _4, capability: W, guide: None, _marker: PhantomData<&()> })
    // PCG: bb2 -> bb4: Lend x to borrow: _13 before bb3[6]:PreMain <before bb3[3]:PreOperands> = &mut  x under conditions bb0 -> bb3
    // ~PCG: bb2 -> bb4: Label place x.snd (Detach)
    // PCG: bb6[1] pre_operands: Remove Edge borrow: _13 before bb3[6]:PreMain <before bb3[3]:PreOperands> = &mut  x under conditions bb0 -> bb3 returning W to x
    let mut x = x0;
    let r: &mut Pair;
    if c {
        drop(x.fst);
        r = &mut z;
    } else {
        r = &mut x;
    }
    r.snd = String::new();
}

// One branch borrows `x` as a whole, the other only `x.fst`: `x.snd` stays
// read while the borrow of `x` lives.
fn borrowed_whole_or_part(c: bool) {
    // ~PCG: bb11[0] pre_operands: Unfreeze x.snd
    // PCG: bb11[4] pre_operands: x.snd: R
    let mut x = Pair { fst: String::new(), snd: String::new() };
    let r: &String;
    if c {
        let t = &x;
        r = &t.snd;
    } else {
        r = &x.fst;
        x.snd = String::new();
    }
    let _ = r.len();
}
