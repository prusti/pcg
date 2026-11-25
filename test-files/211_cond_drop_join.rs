// PCG_EXPECTED_FAILURE: conservation variant_referent_part_lent_discriminant_read
// PCG_EXPECTED_FAILURE: frame array_unpacked_two_ways
// PCG_EXPECTED_FAILURE: frame borrowed_variant_fields_lent_and_read
// PCG_EXPECTED_FAILURE: frame borrowed_variant_nested_referent_part_lent
// PCG_EXPECTED_FAILURE: frame borrowed_variant_referent_lent
// PCG_EXPECTED_FAILURE: frame borrowed_variant_referent_part_lent
// PCG_EXPECTED_FAILURE: frame frozen_array_and_elements_joined
// PCG_EXPECTED_FAILURE: frame frozen_or_referent_lent
// PCG_EXPECTED_FAILURE: frame frozen_whole_or_variant_field_lent
// PCG_EXPECTED_FAILURE: frame variant_field_lent_other_moved
// PCG_EXPECTED_FAILURE: frame variant_field_read_other_variant_borrowed
// PCG_EXPECTED_FAILURE: frame variant_field_read_same_variant_borrowed
// PCG_EXPECTED_FAILURE: frame variant_field_read_same_variant_borrowed_through_ref
// PCG_EXPECTED_FAILURE: frame variant_field_read_sibling_moved
// PCG_EXPECTED_FAILURE: frame variant_fields_lent
// PCG_EXPECTED_FAILURE: frame variant_fields_lent_and_read
// PCG_EXPECTED_FAILURE: frame variant_referent_part_lent_overwritten
// PCG_EXPECTED_FAILURE: frame whole_lent_or_referent_read
// PCG_EXPECTED_FAILURE: frame whole_or_referent_lent
// PCG_EXPECTED_FAILURE: frame whole_or_variant_field_lent
// PCG_EXPECTED_FAILURE: freeze frozen_array_and_elements_joined
// PCG_EXPECTED_FAILURE: freeze variant_field_read_other_variant_borrowed
// PCG_EXPECTED_FAILURE: freeze variant_field_read_other_variant_borrowed_through_ref
// PCG_EXPECTED_FAILURE: freeze variant_field_read_same_variant_borrowed
// PCG_EXPECTED_FAILURE: freeze variant_field_read_same_variant_borrowed_through_ref
// PCG_EXPECTED_FAILURE: freeze variant_referent_part_lent_discriminant_read
// PCG_EXPECTED_FAILURE: label borrowed_frozen_whole_or_part_lent
// PCG_EXPECTED_FAILURE: label borrowed_variant_fields_lent_and_read
// PCG_EXPECTED_FAILURE: label borrowed_whole_or_part
// PCG_EXPECTED_FAILURE: label borrowed_whole_or_part_lent_then_read
// PCG_EXPECTED_FAILURE: label frozen_or_lent
// PCG_EXPECTED_FAILURE: label frozen_or_referent_lent
// PCG_EXPECTED_FAILURE: label frozen_whole_or_part_lent
// PCG_EXPECTED_FAILURE: label frozen_whole_or_variant_field_lent
// PCG_EXPECTED_FAILURE: label moved_or_frozen
// PCG_EXPECTED_FAILURE: label moved_parent_or_frozen
// PCG_EXPECTED_FAILURE: label nested_frozen_or_lent
// PCG_EXPECTED_FAILURE: label read_or_lent
// PCG_EXPECTED_FAILURE: label variant_field_read_other_variant_borrowed
// PCG_EXPECTED_FAILURE: label variant_field_read_other_variant_borrowed_through_ref
// PCG_EXPECTED_FAILURE: label variant_field_read_same_variant_borrowed
// PCG_EXPECTED_FAILURE: label variant_field_read_same_variant_borrowed_through_ref
// PCG_EXPECTED_FAILURE: label variant_field_read_sibling_moved
// PCG_EXPECTED_FAILURE: label variant_field_read_then_moved
// PCG_EXPECTED_FAILURE: label variant_field_read_whole_read
// PCG_EXPECTED_FAILURE: label variant_fields_lent_and_read
// PCG_EXPECTED_FAILURE: label variant_referent_part_lent
// PCG_EXPECTED_FAILURE: label variant_referent_part_lent_overwritten
// PCG_EXPECTED_FAILURE: label whole_lent_or_referent_read
// PCG_EXPECTED_FAILURE: ledger borrowed_frozen_whole_or_part_lent
// PCG_EXPECTED_FAILURE: ledger borrowed_variant_fields_lent_and_read
// PCG_EXPECTED_FAILURE: ledger frozen_or_lent
// PCG_EXPECTED_FAILURE: ledger frozen_or_referent_lent
// PCG_EXPECTED_FAILURE: ledger frozen_whole_or_part_lent
// PCG_EXPECTED_FAILURE: ledger moved_part_or_lent_then_read
// PCG_EXPECTED_FAILURE: ledger nested_frozen_or_lent
// PCG_EXPECTED_FAILURE: ledger variant_fields_lent_and_read
// PCG_EXPECTED_FAILURE: ledger whole_lent_or_referent_read
// PCG_EXPECTED_FAILURE: ledger whole_or_referent_lent
// PCG_EXPECTED_FAILURE: lend borrowed_variant_fields_lent_and_read
// PCG_EXPECTED_FAILURE: lend borrowed_variant_nested_referent_part_lent
// PCG_EXPECTED_FAILURE: lend borrowed_variant_referent_lent
// PCG_EXPECTED_FAILURE: lend borrowed_variant_referent_part_lent
// PCG_EXPECTED_FAILURE: remove-edge array_unpacked_two_ways
// PCG_EXPECTED_FAILURE: remove-edge borrowed_variant_fields_lent_and_read
// PCG_EXPECTED_FAILURE: remove-edge borrowed_variant_nested_referent_part_lent
// PCG_EXPECTED_FAILURE: remove-edge borrowed_variant_referent_lent
// PCG_EXPECTED_FAILURE: remove-edge borrowed_variant_referent_part_lent
// PCG_EXPECTED_FAILURE: remove-edge frozen_whole_or_variant_field_lent
// PCG_EXPECTED_FAILURE: remove-edge variant_field_lent_other_moved
// PCG_EXPECTED_FAILURE: remove-edge variant_field_read_sibling_moved
// PCG_EXPECTED_FAILURE: remove-edge variant_fields_lent
// PCG_EXPECTED_FAILURE: remove-edge variant_fields_lent_and_read
// PCG_EXPECTED_FAILURE: remove-edge whole_or_variant_field_lent
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

// One path moves `s.0`, the other leaves `s` whole; then `s.1`'s contents are
// moved on one branch only. The join holds `s` at W, and `s` as a whole, not
// fully initialised, can be unpacked again at W for its drop.
fn partly_moved_then_partly_moved_again(s: (Option<String>, Option<String>), c: bool) -> usize {
    // PCG: bb12[0] pre_operands: s: W
    let n = if c {
        drop(s.0);
        1
    } else {
        0
    };
    match s.1 {
        Some(x) => x.len() + n,
        None => n,
    }
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

// The elements are frozen apart by the pattern, and reading `arr[0]` freezes
// `arr` too: a join of two paths holding the same keeps both the record of
// `arr` and those of its elements.
fn frozen_array_and_elements_joined(mut arr: [String; 3], c: bool) -> usize {
    // PCG: bb5[0] pre_operands: arr: suspended E
    // PCG: bb5[0] pre_operands: arr[ConstantIndex { offset: 0, min_length: 3, from_end: false }]: suspended E
    // ~PCG: bb3 -> bb5: Weaken suspended arr from E to None
    let [ref mut a, ref b, ..] = arr;
    a.push('z');
    let r = &arr[0];
    let n = if c { 1 } else { 2 };
    r.len() + b.len() + n
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
// lends each field with what it holds, so the join records W for `x.fst` and
// E for `x.snd`, and each gets that back.
fn moved_part_or_lent(c: bool, x0: Pair, mut z: Pair) {
    // PCG: bb2 -> bb4: Lend x.fst to borrow: _13 before bb3[6]:PreMain <before bb3[3]:PreOperands> = &mut  x under conditions bb0 -> bb3
    // PCG: bb2 -> bb4: Lend x.snd to borrow: _13 before bb3[6]:PreMain <before bb3[3]:PreOperands> = &mut  x under conditions bb0 -> bb3
    // ~PCG: bb2 -> bb4: Label place x.snd (Detach)
    // PCG: bb3 -> bb4: Unpack suspended x to x.fst, x.snd
    // PCG: bb3 -> bb4: Weaken suspended x.fst from E to W
    // PCG: bb4[0] pre_operands: x.fst: suspended W
    // PCG: bb4[0] pre_operands: x.snd: suspended E
    // PCG: bb6[1] pre_operands: Remove Edge borrow: _13 before bb3[6]:PreMain <before bb3[3]:PreOperands> = &mut  x under conditions bb0 -> bb3 returning W to x.fst, returning E to x.snd
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

struct P { f: u32, g: u32 }

// One branch freezes `x` for `a`, the other lends it to `m`: when `m` ends,
// `x` is still frozen for `a` and gets its E back only from its unfreeze.
fn frozen_or_lent(c: bool, mut x: P, mut y: P) -> u32 {
    // PCG: bb3[3] post_main: x: R
    // PCG: bb3[3] post_main: x: suspended E
    // ~PCG: bb3[3] post_main: x: E
    // PCG: bb3[5] pre_operands: Unfreeze x
    let a: &u32;
    let m: &mut P;
    if c {
        a = &x.f;
        m = &mut y;
    } else {
        m = &mut x;
        a = &y.f;
    }
    m.g = 1;
    let s = *a;
    s
}

// One branch lends `x` whole, the other only `x.f`: when the loan of `x` ends,
// only `x.g` comes back, and `x.f` comes back when its own loan ends.
fn whole_or_part_lent(c: bool, mut x: P, mut z: P, mut w: u32) -> u32 {
    // PCG: bb3[3] post_main: x.g: E
    // PCG: bb3[3] post_main: x.f: suspended E
    // ~PCG: bb3[3] post_main: x: E
    // PCG: bb3[5] post_main: x: E
    let p: &mut P;
    let q: &mut u32;
    if c {
        p = &mut x;
        q = &mut w;
    } else {
        q = &mut x.f;
        p = &mut z;
    }
    p.g = 1;
    x.g = 2;
    *q = 3;
    w
}

// One branch lends `x` whole, the other each of its fields: the join records
// the fields, and each comes back when its own loan ends.
fn whole_or_every_part_lent(c: bool, mut x: P, mut z: P, mut w: u32, mut v: u32) -> u32 {
    // PCG: bb1 -> bb3: Unpack suspended x to x.f, x.g
    // PCG: bb3[3] post_operands: x.f: suspended E
    // PCG: bb3[3] post_operands: x.g: suspended E
    // PCG: bb3[4] pre_operands: Remove Edge borrow: _18 before bb2[6]:PreMain <before bb2[3]:PreOperands> = &mut  x.f under conditions bb0 -> bb2 returning E to x.f
    // PCG: bb3[5] pre_operands: Remove Edge borrow: _20 before bb2[13]:PreMain <before bb2[10]:PreOperands> = &mut  x.g under conditions bb0 -> bb2 returning E to x.g
    let p: &mut P;
    let q: &mut u32;
    let r: &mut u32;
    if c {
        p = &mut x;
        q = &mut w;
        r = &mut v;
    } else {
        q = &mut x.f;
        r = &mut x.g;
        p = &mut z;
    }
    p.g = 1;
    *q = 3;
    *r = 4;
    x.f + w
}

struct Q { a: u32, b: u32 }
struct N { f: Q, g: u32 }

// One branch freezes `x` for a borrow of `x.f.a`, the other lends `x` whole:
// when the loan of `x` ends, `x` comes back frozen at every level.
fn nested_frozen_or_lent(c: bool, mut x: N, mut y: N) -> u32 {
    // PCG: bb3[3] post_operands: x: R
    // PCG: bb3[3] post_operands: x: suspended E
    // PCG: bb3[3] post_operands: x.f: R
    // PCG: bb3[3] post_operands: x.f.a: R
    // PCG: bb3[3] post_operands: x.f.b: R
    // PCG: bb3[3] post_operands: x.g: R
    // PCG: bb3[3] pre_main: Refreeze x to x.f.a
    let a: &u32;
    let m: &mut N;
    if c {
        a = &x.f.a;
        m = &mut y;
    } else {
        m = &mut x;
        a = &y.f.a;
    }
    m.g = 1;
    x.g = 5;
    x.f.b = 6;
    let s = *a;
    x.f.a = 7;
    s
}

struct S<'a> { f: &'a mut u32, g: u32 }

// One branch lends `x` whole, the other the referent of `x.f`: when the loan
// of `x` ends, `x.f` comes back with its referent still lent (e), and the
// referent comes back when its own loan ends.
fn whole_or_referent_lent<'a>(c: bool, mut x: S<'a>, mut z: S<'a>, mut w: u32) -> u32 {
    // PCG: bb1 -> bb3: Unpack suspended x to x.f, x.g
    // PCG: bb1 -> bb3: Unpack suspended x.f to *x.f
    // PCG: bb3[3] post_operands: x.f: e
    // PCG: bb3[3] post_operands: x.g: E
    // PCG: bb3[3] post_operands: *x.f: suspended E
    // PCG: bb3[5] pre_operands: Remove Edge borrow: _14 before bb2[6]:PreMain <before bb2[3]:PreOperands> = &mut  *x.f under conditions bb0 -> bb2 returning E to *x.f
    let p: &mut S<'a>;
    let q: &mut u32;
    if c {
        p = &mut x;
        q = &mut w;
    } else {
        q = &mut *x.f;
        p = &mut z;
    }
    p.g = 1;
    x.g = 2;
    *q = 3;
    *x.f + w
}

// As `whole_or_part_lent`, with the lent place behind a reference.
fn borrowed_whole_or_part_lent(c: bool, x: &mut P, mut z: P, mut w: u32) -> u32 {
    // PCG: bb1 -> bb3: Unpack suspended *x to (*x).f, (*x).g
    // PCG: bb3[3] post_operands: (*x).f: suspended E
    // PCG: bb3[3] post_operands: (*x).g: E
    // PCG: bb3[5] pre_operands: Remove Edge borrow: _14 before bb2[6]:PreMain <before bb2[3]:PreOperands> = &mut  (*x).f under conditions bb0 -> bb2 returning E to (*x).f
    let p: &mut P;
    let q: &mut u32;
    if c {
        p = &mut *x;
        q = &mut w;
    } else {
        q = &mut x.f;
        p = &mut z;
    }
    p.g = 1;
    x.g = 2;
    *q = 3;
    x.f + w
}

enum AB { A(u32, u32), B }

// One branch lends `x` whole, the other a field of its variant `A`: the join
// records `x` (not every path matched `A`), which comes back whole.
fn whole_or_variant_field_lent(c: bool, mut x: AB, mut z: AB, mut w: u32) -> u32 {
    // PCG: bb6 -> bb7: Pack suspended x
    // PCG: bb8[5] post_operands: x: suspended E
    // PCG: bb8[7] pre_operands: Remove Edge borrow: s before bb6[7]:PreMain <before bb6[3]:PreOperands> = &mut  x@A.0 under conditions bb0 -> bb2, bb2 -> bb4 returning E to x
    // PCG: bb8[7] post_operands: x: E
    let p: &mut AB;
    let q: &mut u32;
    if c {
        p = &mut x;
        q = &mut w;
    } else {
        match x {
            AB::A(ref mut s, _) => q = s,
            AB::B => q = &mut w,
        }
        p = &mut z;
    }
    *p = AB::B;
    *q = 3;
    match x { AB::A(s, t) => s + t, AB::B => w }
}

// One branch freezes `x` whole for `a`, the other lends `x.f` to `m`: the
// first moves the freeze to the fields, and when `m` ends `x.f` comes back
// frozen while `a` lives.
fn frozen_whole_or_part_lent(c: bool, mut x: P, mut y: P) -> u32 {
    // ~PCG: bb1 -> bb3: Unfreeze x
    // PCG: bb1 -> bb3: Lend x.f to borrow: _13 before bb2[6]:PreMain <before bb2[3]:PreOperands> = &mut  x.f under conditions bb0 -> bb2
    // PCG: bb3[3] pre_operands: Remove Edge borrow: _13 before bb2[6]:PreMain <before bb2[3]:PreOperands> = &mut  x.f under conditions bb0 -> bb2 returning R to x.f
    // ~PCG: bb3[3] pre_operands: Unfreeze x.f
    // PCG: bb3[3] pre_operands: Pack suspended x
    // PCG: bb3[3] post_operands: x: R
    // PCG: bb3[3] post_operands: x: suspended E
    // PCG: bb3[5] pre_operands: Unfreeze x
    let a: &P;
    let m: &mut u32;
    if c {
        a = &x;
        m = &mut y.f;
    } else {
        m = &mut x.f;
        a = &y;
    }
    *m = 1;
    let s = a.g;
    x.f = 2;
    x.g = 3;
    s + x.f + x.g
}

// As `frozen_whole_or_part_lent`, with `x` behind a reference.
fn borrowed_frozen_whole_or_part_lent(c: bool, x: &mut P, y: P, mut w: u32) -> u32 {
    // PCG: bb3[0] post_operands: (*x).g: R
    // ~PCG: bb3[0] pre_operands: Unfreeze (*x).g
    // PCG: bb3[3] pre_operands: Remove Edge borrow: _14 before bb2[6]:PreMain <before bb2[3]:PreOperands> = &mut  (*x).f under conditions bb0 -> bb2 returning R to (*x).f
    // PCG: bb3[3] pre_operands: Pack suspended *x
    // PCG: bb3[3] post_operands: *x: R
    // PCG: bb3[3] post_operands: *x: suspended E
    // PCG: bb3[5] pre_operands: Unfreeze *x
    let a: &P;
    let m: &mut u32;
    if c {
        a = &*x;
        m = &mut w;
    } else {
        m = &mut x.f;
        a = &y;
    }
    *m = 1;
    let s = a.g;
    x.f = 2;
    s + x.f + w
}

enum AC { A(u32, u32), C(u32) }

// Each arm lends a field of a different variant: the join records the enum.
fn variant_fields_lent(mut x: AC) -> u32 {
    // PCG: bb3 -> bb5: Pack suspended x
    // PCG: bb4 -> bb5: Pack suspended x
    // PCG: bb5[5] post_operands: x: E
    let q: &mut u32 = match x {
        AC::A(ref mut s, _) => s,
        AC::C(ref mut t) => t,
    };
    *q = 3;
    match x {
        AC::A(s, t) => s + t,
        AC::C(t) => t,
    }
}

// One branch freezes `x` whole, the other lends a field of its variant `A`:
// the frozen `x` stays lent to `a`, and comes back frozen while `a` lives.
fn frozen_whole_or_variant_field_lent(c: bool, mut x: AB, z: AB, mut w: u32) -> u32 {
    // PCG: bb1 -> bb8: Lend x to borrow: _10 before bb1[6]:PreMain = & x under conditions bb0 -> bb1
    // ~PCG: bb1 -> bb8: Label place x (Detach)
    // PCG: bb8[3] pre_operands: Remove Edge borrow: s before bb6[7]:PreMain <before bb6[3]:PreOperands> = &mut  x@A.0 under conditions bb0 -> bb2, bb2 -> bb4 returning R to x
    // PCG: bb9[1] pre_operands: Unfreeze x
    let a: &AB;
    let q: &mut u32;
    if c {
        a = &x;
        q = &mut w;
    } else {
        match x {
            AB::A(ref mut s, _) => q = s,
            AB::B => q = &mut w,
        }
        a = &z;
    }
    *q = 3;
    let r = match a {
        AB::A(s, _) => *s,
        AB::B => 0,
    };
    x = AB::B;
    r + match x {
        AB::A(s, t) => s + t,
        AB::B => w,
    }
}

// One arm lends a field of `x`'s variant `A` mutably and the other field
// shared: at the join the shared field stays lent to its own borrow, so when
// the mutable loan ends `x` comes back frozen while the shared one lives.
fn variant_fields_lent_and_read(mut x: AB, mut w: u32) -> u32 {
    // PCG: bb4 -> bb5: Lend x@A.1 to borrow: b before bb4[13]:PreMain = & x@A.1 under conditions bb0 -> bb2
    // ~PCG: bb4 -> bb5: Label place x@A.1 (Detach)
    // PCG: bb5[2] post_operands: x: R
    // PCG: bb5[2] post_operands: x: suspended E
    // PCG: bb5[2] post_operands: x@A.0: R
    // PCG: bb5[2] post_operands: x@A.1: R
    let q: &mut u32;
    let r: &u32;
    let v = 5;
    match x {
        AB::A(ref mut a, ref b) => {
            q = a;
            r = b;
        }
        AB::B => {
            q = &mut w;
            r = &v;
        }
    }
    *q = 3;
    let t = match x {
        AB::A(a, _) => a,
        AB::B => 0,
    };
    t + *r
}

// As `variant_fields_lent_and_read`, with `x` behind a reference.
fn borrowed_variant_fields_lent_and_read(x: &mut AB, mut w: u32) -> u32 {
    // PCG: bb4 -> bb5: Lend (*x)@A.1 to borrow: b before bb4[13]:PreMain = & (*x)@A.1 under conditions bb0 -> bb2
    // ~PCG: bb5[0] post_operands: *x: R
    // PCG: bb5[2] post_operands: *x: R
    // PCG: bb5[2] post_operands: *x: suspended E
    // PCG: bb5[2] post_operands: (*x)@A.0: R
    let q: &mut u32;
    let r: &u32;
    let v = 5;
    match *x {
        AB::A(ref mut a, ref b) => {
            q = a;
            r = b;
        }
        AB::B => {
            q = &mut w;
            r = &v;
        }
    }
    *q = 3;
    let t = match *x {
        AB::A(a, _) => a,
        AB::B => 0,
    };
    t + *r
}

// One branch lends `x` whole, the other reads the referent of `x.f`: when the
// loan of `x` ends, `x` comes back frozen down to the referent.
fn whole_lent_or_referent_read<'a>(c: bool, mut x: S<'a>, mut z: S<'a>, w: u32) -> u32 {
    // PCG: bb3[3] post_operands: x: R
    // PCG: bb3[3] post_operands: x: suspended E
    // PCG: bb3[3] post_operands: x.f: R
    // PCG: bb3[3] post_operands: *x.f: R
    // PCG: bb3[3] pre_main: Refreeze x to *x.f
    let p: &mut S<'a>;
    let a: &u32;
    if c {
        p = &mut x;
        a = &w;
    } else {
        a = &*x.f;
        p = &mut z;
    }
    p.g = 1;
    x.g = 2;
    let s = *a;
    *x.f = 3;
    s + x.g
}

// One branch moves `x.fst` out, the other lends `x` whole; `x.snd` is read
// after the loan: it comes back E.
fn moved_part_or_lent_then_read(c: bool, mut x: Pair, mut z: Pair) -> usize {
    // PCG: bb3 -> bb4: Lend x.fst to borrow: _8 before bb1[6]:PreMain <before bb1[3]:PreOperands> = &mut  x under conditions bb0 -> bb1
    // PCG: bb3 -> bb4: Lend x.snd to borrow: _8 before bb1[6]:PreMain <before bb1[3]:PreOperands> = &mut  x under conditions bb0 -> bb1
    // PCG: bb5[0] post_operands: x.fst: W
    // PCG: bb5[0] post_operands: x.snd: E
    let p: &mut Pair;
    if c {
        p = &mut x;
    } else {
        drop(x.fst);
        p = &mut z;
    }
    p.snd.push('a');
    x.fst = String::new();
    x.fst.len() + x.snd.len()
}

enum AS { A(u32, String), B }

// One arm lends a field of `x`'s variant `A` and moves the other: the moved
// field goes with the loan, so `x` comes back W.
fn variant_field_lent_other_moved(mut x: AS, mut w: u32) -> u32 {
    // PCG: bb6 -> bb7: Lend x@A.1 to borrow: s before bb6[1]:PreMain <before bb4[5]:PreOperands> = &mut  x@A.0 under conditions bb0 -> bb2
    // PCG: bb3 -> bb7: Weaken suspended x from E to W
    // PCG: bb7[2] post_operands: x: W
    let q: &mut u32;
    match x {
        AS::A(ref mut s, t) => {
            q = s;
            drop(t);
        }
        AS::B => q = &mut w,
    }
    *q = 3;
    x = AS::B;
    w
}

// A variant field is read on one path only, then its sibling is moved on one
// path only. Where `x` is frozen, the meet with the moved path's W is none:
// the loan of `x@A.0` is in the value of `x`, so `x` is lent and comes back
// W.
fn variant_field_read_sibling_moved(x: AS) -> u32 {
    // PCG: bb8 -> bb10: Lend x to borrow: p before bb2[7]:PreMain = & x@A.0 under conditions bb0 -> bb1, bb4 -> bb8
    // PCG: bb8 -> bb10: Weaken suspended x from E to W
    let y = 0;
    let mut a: &u32 = &y;
    if let AS::A(ref p, _) = x {
        a = p;
    }
    if let AS::A(_, t) = x {
        drop(t);
    }
    *a
}

// One branch freezes `x` whole, the other lends the referent of `x.f`: `x.f`
// holds nothing at the join (neither its R under the live freeze nor e), and
// `x` comes back E once both loans end.
fn frozen_or_referent_lent<'a>(c: bool, mut x: S<'a>, z: S<'a>, mut w: u32) -> u32 {
    // ~PCG: bb3[0] post_operands: x.f: e
    // PCG: bb3[3] post_operands: x: R
    // PCG: bb3[3] post_operands: x: suspended E
    // PCG: bb3[5] pre_operands: Unfreeze x
    // PCG: bb3[6] post_main: x.f: E
    // PCG: bb3[6] post_main: x.g: E
    let a: &S<'a>;
    let m: &mut u32;
    if c {
        a = &x;
        m = &mut w;
    } else {
        m = &mut *x.f;
        a = &z;
    }
    *m = 1;
    let s = a.g;
    x.g = 2;
    *x.f = 3;
    s
}

// The branches unpack `x` at different indices: the join records `x`, which
// comes back whole.
fn array_unpacked_two_ways(c: bool, mut x: [u32; 4], i: usize, w: u32) -> u32 {
    // PCG: bb1 -> bb4: Pack suspended x
    // PCG: bb3 -> bb4: Pack suspended x
    // PCG: bb4[3] post_operands: x: E
    let q: &mut u32;
    if c {
        let [ref mut a, ..] = x;
        q = a;
    } else {
        q = &mut x[i];
    }
    *q = 1;
    x[0] + w
}

// As `borrowed_whole_or_part_lent`, with the part's loan ending first: the
// parts' records pack into `*x` when its unpacking goes, and `*x` comes back
// E when the loan of `*x` ends.
fn borrowed_whole_or_part_lent_then_read(c: bool, x: &mut P, mut z: P, mut w: u32) -> u32 {
    // PCG: bb3[3] pre_operands: Pack suspended *x
    // PCG: bb3[3] post_operands: *x: suspended E
    // PCG: bb3[4] pre_operands: Remove Edge borrow: _10 before bb1[6]:PreMain <before bb1[3]:PreOperands> = &mut  *x under conditions bb0 -> bb1 returning E to *x
    // PCG: bb3[4] post_operands: x: E
    let p: &mut P;
    let q: &mut u32;
    if c {
        p = &mut *x;
        q = &mut w;
    } else {
        q = &mut x.f;
        p = &mut z;
    }
    *q = 3;
    p.g = 1;
    let r: &P = &*x;
    r.f + w
}

// A variant field is borrowed on one path only: the join holds `x` frozen and
// packed, with the layout of the borrowed field below it. Borrowing the other
// variant mutably (allowed: variants are disjoint) moves the freeze to `x@A`
// without entering it, and `x@C` gets E.
fn variant_field_read_other_variant_borrowed(mut x: AC) -> u32 {
    // PCG: bb3 -> bb4: Freeze x
    // PCG: bb6[1] pre_operands: unpack x@C with capability R
    // PCG: bb6[1] pre_operands: Refreeze x to x@A
    let y = 0;
    let mut a: &u32 = &y;
    if let AC::A(ref p, _) = x {
        a = p;
    }
    if let AC::C(ref mut q) = x {
        *q = 1;
    }
    *a
}

// As above, re-matching the same variant: the freeze moves to `x@A.0` and
// `x@A.1` gets E.
fn variant_field_read_same_variant_borrowed(mut x: AC) -> u32 {
    // PCG: bb6[1] pre_operands: unpack x@A with capability R
    // PCG: bb6[1] pre_operands: Refreeze x to x@A.0
    let y = 0;
    let mut a: &u32 = &y;
    if let AC::A(ref p, _) = x {
        a = p;
    }
    if let AC::A(_, ref mut q) = x {
        *q = 1;
    }
    *a
}

// As above, borrowing `x` whole for read: when that borrow ends `x` stays
// frozen, since the loan of `x@A.0` still lives.
fn variant_field_read_whole_read(x: AC) -> u32 {
    // PCG: bb4[5] pre_operands: Remove Edge borrow: r = & x
    // ~PCG: bb4[5] pre_operands: Unfreeze x
    let y = 0;
    let mut a: &u32 = &y;
    if let AC::A(ref p, _) = x {
        a = p;
    }
    let r = &x;
    let _ = r;
    *a
}

// A variant field is a mutable reference whose referent is partly lent on
// one path only, and `o` is W on the other. The loan lies behind the
// reference, so it does not keep `o` from being overwritten: the join holds
// `o` at W, and the path with the loan labels the value it borrows from.
fn variant_referent_part_lent(x: &mut (u32, u32)) -> Option<&mut u32> {
    // PCG: bb4 -> bb5: Label place o@Some.0 (Write)
    // PCG: bb4 -> bb5: Weaken o@Some.0 from e to W
    // PCG: bb5[0] pre_operands: o: W
    let o = Some(x);
    match o {
        Some(&mut (_, ref mut v)) => Some(v),
        None => None,
    }
}

// As above, with `o` overwritten while the loan lives and used afterwards.
fn variant_referent_part_lent_overwritten(x: &mut (u32, u32)) -> u32 {
    // PCG: bb5[11] pre_main: o: W
    let mut o = Some(x);
    let v = match o {
        Some(&mut (_, ref mut v)) => Some(v),
        None => None,
    };
    let mut z = (0, 0);
    o = Some(&mut z);
    if let Some(r) = &mut o {
        r.0 += 1;
    }
    if let Some(v) = v {
        *v += 1;
    }
    match o {
        Some(r) => r.0,
        None => 0,
    }
}

// As `variant_referent_part_lent`, behind a reference. The other path records
// E for `*x`; this path records e for the reference `(*x)@Some.0` and E for
// the parts of its referent, which pack into E, so `x` comes back E when the
// loan ends.
fn borrowed_variant_referent_part_lent(x: &mut Option<&mut (u32, u32)>) -> u32 {
    // PCG: bb4 -> bb5: Pack suspended *x
    // PCG: bb5[0] pre_operands: *x: suspended E
    // PCG: bb10[0] pre_operands: x: E
    let v = match *x {
        Some(&mut (_, ref mut v)) => Some(v),
        None => None,
    };
    if let Some(v) = v {
        *v += 1;
    }
    match x {
        Some(r) => r.0,
        None => 0,
    }
}

// As above, with the referent lent whole: the referent is a leaf of the
// layout of `*x` that holds nothing, so the join holds nothing at `*x` and
// records E for it.
fn borrowed_variant_referent_lent(x: &mut Option<&mut (u32, u32)>) -> u32 {
    // PCG: bb4 -> bb5: Pack suspended *x
    // PCG: bb5[0] pre_operands: *x: suspended E
    // PCG: bb10[0] pre_operands: x: E
    let v = match *x {
        Some(&mut ref mut b) => Some(b),
        None => None,
    };
    if let Some(v) = v {
        v.1 += 1;
    }
    match x {
        Some(r) => r.0,
        None => 0,
    }
}

// As `borrowed_variant_referent_part_lent`, through a reference inside the
// referent: the inner reference packs into E first.
fn borrowed_variant_nested_referent_part_lent(x: &mut Option<&mut (u32, &mut (u32, u32))>) -> u32 {
    // PCG: bb5[0] pre_operands: *x: suspended E
    // PCG: bb10[0] pre_operands: x: E
    let v = match *x {
        Some(&mut (_, &mut (_, ref mut v))) => Some(v),
        None => None,
    };
    if let Some(v) = v {
        *v += 1;
    }
    match x {
        Some(r) => r.0,
        None => 0,
    }
}

// A variant field is borrowed on one path only, as in
// `variant_field_read_other_variant_borrowed`, and `x` is moved after the loan
// of `x@A.0` ends: `x` is unfrozen and the layout below it is forgotten, not
// collapsed.
fn variant_field_read_then_moved(x: AC) -> AC {
    // PCG: bb4[2] pre_operands: Unfreeze x
    // PCG: bb4[3] pre_operands: x: W
    let y = 0;
    let mut a: &u32 = &y;
    if let AC::A(ref p, _) = x {
        a = p;
    }
    let _ = *a;
    x
}

// As `variant_field_read_other_variant_borrowed`, behind a reference: the
// layout of the borrowed field is unpackings in the borrow PCG.
fn variant_field_read_other_variant_borrowed_through_ref(x: &mut AC) -> u32 {
    // PCG: bb6[1] pre_operands: Refreeze x to *x
    // PCG: bb6[1] pre_operands: Refreeze *x to (*x)@A
    // PCG: bb6[1] pre_operands: (*x)@C.0: E
    let y = 0;
    let mut a: &u32 = &y;
    if let AC::A(ref p, _) = *x {
        a = p;
    }
    if let AC::C(ref mut q) = *x {
        *q = 1;
    }
    *a
}

// As `variant_field_read_same_variant_borrowed`, behind a reference: the
// freeze of `x` moves to `*x`, and from there to `(*x)@A.0`.
fn variant_field_read_same_variant_borrowed_through_ref(x: &mut AC) -> u32 {
    // PCG: bb6[1] pre_operands: Refreeze x to *x
    // PCG: bb6[1] pre_operands: Refreeze *x to (*x)@A.0
    // PCG: bb6[1] pre_operands: (*x)@A.1: E
    let y = 0;
    let mut a: &u32 = &y;
    if let AC::A(ref p, _) = *x {
        a = p;
    }
    if let AC::A(_, ref mut q) = *x {
        *q = 1;
    }
    *a
}

// The discriminant of `o` is read while `v` borrows into its referent: the
// read is shallow (rustc allows it) and `o` comes back whole once `v` ends.
pub fn variant_referent_part_lent_discriminant_read(
    mut o: Option<&mut (u32, u32)>,
) -> Option<&mut (u32, u32)> {
    // PCG: bb5[6] pre_operands: o: R
    // PCG: bb9[2] pre_operands: Unfreeze o
    let mut z = 0;
    let v: &mut u32 = match o {
        Some(&mut (_, ref mut v)) => v,
        None => &mut z,
    };
    let s = matches!(o, Some(_));
    *v = 1;
    if s { o } else { None }
}
