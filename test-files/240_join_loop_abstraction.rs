// PCG_EXPECTED_FAILURE: cycle <TrimmedFieldsWith<'a, F> as std::iter::Iterator>::next
// PCG_EXPECTED_FAILURE: cycle referent_of_array_element_borrowed_across_loop
// PCG_EXPECTED_FAILURE: cycle referent_of_element_borrowed_across_loop
// PCG_EXPECTED_FAILURE: cycle referent_of_element_borrowed_in_for_loop
// PCG_EXPECTED_FAILURE: cycle rename_variants
// PCG_EXPECTED_FAILURE: frame <CharIndices<'a> as std::iter::Iterator>::next
// PCG_EXPECTED_FAILURE: frame <FieldsWith<'a, F> as std::iter::Iterator>::next
// PCG_EXPECTED_FAILURE: frame <TrimmedFieldsWith<'a, F> as std::iter::Iterator>::next
// PCG_EXPECTED_FAILURE: frame Node::at
// PCG_EXPECTED_FAILURE: frame element_read_across_loop_beside_frozen_elements
// PCG_EXPECTED_FAILURE: frame part_or_whole_lent_through_ref
// PCG_EXPECTED_FAILURE: frame referent_of_array_element_borrowed_across_loop
// PCG_EXPECTED_FAILURE: frame referent_of_element_borrowed_across_loop
// PCG_EXPECTED_FAILURE: frame referent_of_element_borrowed_in_for_loop
// PCG_EXPECTED_FAILURE: frame rename_variants
// PCG_EXPECTED_FAILURE: frame variant_blocker_lifetime
// PCG_EXPECTED_FAILURE: frame variant_field_shared_across_loop
// PCG_EXPECTED_FAILURE: frame variant_field_shared_across_loop_in_array
// PCG_EXPECTED_FAILURE: frame variant_field_shared_across_loop_in_array_then_written
// PCG_EXPECTED_FAILURE: frame variant_field_shared_across_loop_then_loop_mut_other
// PCG_EXPECTED_FAILURE: frame variant_field_shared_then_overwritten
// PCG_EXPECTED_FAILURE: freeze element_read_across_loop_beside_frozen_elements
// PCG_EXPECTED_FAILURE: freeze variant_field_shared_across_loop
// PCG_EXPECTED_FAILURE: freeze variant_field_shared_across_loop_in_array
// PCG_EXPECTED_FAILURE: freeze variant_field_shared_across_loop_in_array_then_written
// PCG_EXPECTED_FAILURE: freeze variant_field_shared_across_loop_then_loop_mut_other
// PCG_EXPECTED_FAILURE: freeze variant_field_shared_across_loop_through_ref
// PCG_EXPECTED_FAILURE: freeze variant_field_shared_before_loop_through_ref
// PCG_EXPECTED_FAILURE: freeze variant_field_shared_then_overwritten
// PCG_EXPECTED_FAILURE: label <FieldsWith<'a, F> as std::iter::Iterator>::next
// PCG_EXPECTED_FAILURE: label <TrimmedFieldsWith<'a, F> as std::iter::Iterator>::next
// PCG_EXPECTED_FAILURE: label Node::at
// PCG_EXPECTED_FAILURE: label element_read_across_loop_beside_frozen_elements
// PCG_EXPECTED_FAILURE: label frozen_before_loop
// PCG_EXPECTED_FAILURE: label part_or_whole_lent
// PCG_EXPECTED_FAILURE: label part_or_whole_lent_through_ref
// PCG_EXPECTED_FAILURE: label shared_loan_ends_in_loop
// PCG_EXPECTED_FAILURE: label shared_or_mutable
// PCG_EXPECTED_FAILURE: label variant_blocker_lifetime
// PCG_EXPECTED_FAILURE: label variant_field_shared_across_loop
// PCG_EXPECTED_FAILURE: label variant_field_shared_across_loop_in_array
// PCG_EXPECTED_FAILURE: label variant_field_shared_across_loop_in_array_then_written
// PCG_EXPECTED_FAILURE: label variant_field_shared_across_loop_other_variant_read
// PCG_EXPECTED_FAILURE: label variant_field_shared_across_loop_then_loop_mut_other
// PCG_EXPECTED_FAILURE: label variant_field_shared_across_loop_then_moved
// PCG_EXPECTED_FAILURE: label variant_field_shared_across_loop_through_ref
// PCG_EXPECTED_FAILURE: label variant_field_shared_before_loop_through_ref
// PCG_EXPECTED_FAILURE: label variant_field_shared_then_overwritten
// PCG_EXPECTED_FAILURE: label variant_fields_shared_across_loop_end_apart
// PCG_EXPECTED_FAILURE: lend part_or_whole_lent_through_ref
// PCG_EXPECTED_FAILURE: unfreeze frozen_before_loop
// PCG_EXPECTED_FAILURE: unfreeze shared_loan_ends_in_loop
// PCG_EXPECTED_FAILURE: unfreeze variant_field_shared_across_loop_then_loop_mut_other
// PCG_EXPECTED_FAILURE: unfreeze variant_field_shared_before_loop_through_ref
struct List<'a> {
    head: &'a mut i32,
    tail: Option<Box<List<'a>>>,
}

fn consume(mut list: List<'_>) {
    // PCG_LIFETIME_DISPLAY: list 0 'a
    // Constructing the loop abstraction again after normalizing the owned
    // state loses the current root and weakens its capabilities.
    // PCG: bb1[0] pre_operands: list: E
    // PCG: bb1[0] pre_operands: Loop(bb1): Remote(_1)↓'a -> list↓'a
    // Preserve the sibling field when the loop abstracts the path through
    // tail: it stays connected to the remote projection through `list`.
    // PCG: bb1[0] pre_operands: list.head before bb1[0]:PreOperands↓'a -> list↓'a
    // PCG: bb1[0] pre_operands: Loop(bb1): Remote(_1)↓'a -> list.tail@Some.0↓'a
    // The loop head does not unpack `list.tail` to `Some`: the path that
    // leaves the loop did not match it.
    // ~PCG: bb1[0] pre_operands: list.tail@Some before bb1[0]:PreOperands↓'a -> list.tail before bb1[0]:PreOperands↓'a
    while let Some(tail) = list.tail {
        list = *tail;
    }
}

fn consume_after_branch<'a>(mut list: List<'a>, other: List<'a>, choose_other: bool) {
    // PCG_LIFETIME_DISPLAY: list 0 'list
    // PCG_LIFETIME_DISPLAY: other 0 'other
    // Preserve both possible roots when abstracting the loop after the branch.
    // PCG: bb7[0] pre_operands: list: E
    // PCG: bb7[0] pre_operands: Loop(bb7): Remote(_1)↓'list -> list↓'list
    // PCG: bb7[0] pre_operands: Loop(bb7): Remote(_2)↓'other -> list↓'list
    // PCG: bb7[0] pre_operands: list.head before bb7[0]:PreOperands↓'list -> list↓'list
    // Collapsing one child must preserve the path from the remote projections to tail.
    // PCG: bb7[0] pre_operands: Loop(bb7): Remote(_1)↓'list -> list.tail@Some.0↓'list
    // PCG: bb7[0] pre_operands: Loop(bb7): Remote(_2)↓'other -> list.tail@Some.0↓'list
    if choose_other {
        list = other;
    }
    while let Some(tail) = list.tail {
        list = *tail;
    }
}

pub struct CharIndices<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Iterator for CharIndices<'a> {
    type Item = (usize, usize, char);

    fn next(&mut self) -> Option<(usize, usize, char)> {
        let b = *self.bytes.get(self.at)?;
        self.at += 1;
        Some((self.at - 1, self.at, b as char))
    }
}

pub struct FieldsWith<'a, F> {
    f: F,
    bytes: &'a [u8],
    chars: CharIndices<'a>,
}

// The `for` loop borrows only `self.chars`. The lifetime `iter` shares with
// `self.bytes` makes `*self` a root of the loop, but the loop lends only
// `(*self).chars`, not all of `*self`, whose other fields hold E.
impl<'a, F: FnMut(char) -> bool> Iterator for FieldsWith<'a, F> {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<&'a [u8]> {
        // PCG_LIFETIME_DISPLAY: iter 0 'iter
        // PCG: bb3[0] pre_operands: Loop(bb3): (*self).chars -> iter↓'iter
        // ~PCG: bb3[0] pre_operands: Loop(bb3): *self -> iter↓'iter
        // PCG: bb3[0] pre_operands: (*self).f: E
        // PCG: bb3[0] pre_operands: (*self).bytes: E
        let mut end = 0;
        for (_, e, ch) in self.chars.by_ref() {
            if (self.f)(ch) {
                break;
            }
            end = e;
        }
        Some(&self.bytes[0..end])
    }
}

pub struct Node {
    prefix: Vec<u8>,
    children: Vec<Node>,
    wild: bool,
}

struct Skipped<'n, 'p> {
    node: &'n Node,
    path: &'p [u8],
}

impl Node {
    // `self` is dead in the loops; the body weakens it, so the inner loop
    // head holds it with W.
    pub fn at<'n, 'p>(&'n self, mut path: &'p [u8]) -> Option<&'n Node> {
        // PCG: bb1 -> bb2: Weaken self from E to W
        // PCG: bb2[0] pre_operands: self: W
        let mut node = self;
        let mut skipped: Vec<Skipped<'_, '_>> = Vec::new();
        'backtrack: loop {
            'walk: loop {
                if path.len() <= node.prefix.len() {
                    if *path == *node.prefix {
                        return Some(node);
                    }
                    break 'walk;
                }
                let previous = path;
                path = &path[node.prefix.len()..];
                if node.wild {
                    skipped.push(Skipped { node, path: previous });
                    node = &node.children[0];
                    continue 'walk;
                }
                break 'walk;
            }
            while let Some(s) = skipped.pop() {
                node = s.node;
                path = s.path;
                continue 'backtrack;
            }
            return None;
        }
    }
}

struct P {
    f: i32,
    g: i32,
}

// The loop lends `x` while `a` may still borrow it, so the loop head holds
// `x` frozen although an iteration writes `x.g` after `a` is reassigned.
fn shared_loan_ends_in_loop(n: i32) -> i32 {
    // PCG: bb1[0] pre_operands: x.f: R
    // PCG: bb1[0] pre_operands: x.f: suspended E
    // PCG: bb1[0] pre_operands: x.g: R
    // PCG: bb1[0] pre_operands: x.g: suspended E
    // ~PCG: bb1[0] pre_operands: x.g: E
    // The iteration that reassigns `a` gets `x` back, and the back edge
    // freezes it again.
    // PCG: bb4[0] pre_operands: Unfreeze x.g
    // PCG: bb4[0] pre_operands: x.g: E
    // PCG: bb4 -> bb6: Freeze x.g
    // Nothing is lost when the loop exits.
    // PCG: bb10[0] pre_operands: x: E
    let mut x = P { f: 0, g: 0 };
    let z = P { f: 1, g: 2 };
    let mut a = &x;
    let mut s = 0;
    let mut i = 0;
    while i < n {
        if i == 3 {
            a = &z;
            x.g = 1;
        }
        s += a.g + x.g;
        i += 1;
    }
    s
}

// One iteration lends `x.f` mutably, another `x` whole: neither part holds a
// capability at the loop head.
fn part_or_whole_lent(n: i32) -> i32 {
    // PCG_LIFETIME_DISPLAY: a 0 'a
    // PCG: bb0 -> bb1: Lend x to Loop(bb1): x -> a↓'a
    // PCG: bb1[0] pre_operands: x.f: suspended E
    // PCG: bb1[0] pre_operands: x.g: suspended E
    // ~PCG: bb1[0] pre_operands: x.g: E
    // PCG: bb5[0] pre_operands: x: E
    let mut x = P { f: 0, g: 0 };
    let mut y = 0;
    let mut a: &mut i32 = &mut y;
    let mut i = 0;
    while i < n {
        *a += 1;
        if i % 2 == 0 {
            a = &mut x.f;
        } else {
            let w = &mut x;
            a = &mut w.g;
        }
        i += 1;
    }
    *a
}

fn part_or_whole_lent_through_ref(x: &mut P, n: i32) -> i32 {
    // PCG_LIFETIME_DISPLAY: a 0 'a
    // PCG: bb0 -> bb1: Lend *x to Loop(bb1): *x -> a↓'a
    // PCG: bb1[0] pre_operands: (*x).f: suspended E
    // PCG: bb1[0] pre_operands: (*x).g: suspended E
    // ~PCG: bb1[0] pre_operands: (*x).g: E
    // PCG: bb5[0] pre_operands: x: E
    let mut y = 0;
    let mut a: &mut i32 = &mut y;
    let mut i = 0;
    while i < n {
        *a += 1;
        if i % 2 == 0 {
            a = &mut x.f;
        } else {
            let w = &mut *x;
            a = &mut w.g;
        }
        i += 1;
    }
    *a
}

// One iteration borrows `x.f` shared, another `x` mutably: the loop head
// lends `x` as for a mutable loan.
fn shared_or_mutable(n: i32) -> i32 {
    // PCG_LIFETIME_DISPLAY: a 0 'a
    // PCG: bb0 -> bb1: Lend x to Loop(bb1): x -> a↓'a
    // ~PCG: bb0 -> bb1: Weaken suspended x from E to None
    // PCG: bb1[0] pre_operands: x: suspended E
    // ~PCG: bb1[0] pre_operands: x.f: R
    // PCG: bb12[0] pre_operands: x: E
    let mut x = P { f: 0, g: 0 };
    let y = 0;
    let mut a: &i32 = &y;
    let mut i = 0;
    let mut s = 0;
    while i < n {
        s += *a;
        if i % 2 == 0 {
            a = &x.f;
        } else {
            let w = &mut x;
            w.g += 1;
            a = &w.f;
        }
        i += 1;
    }
    s
}

// `x.f` is frozen before the loop by a shared loan that ends inside it.
fn frozen_before_loop(n: i32) -> i32 {
    // PCG: bb1[0] pre_operands: x.f: R
    // PCG: bb1[0] pre_operands: x.f: suspended E
    // PCG: bb1[0] pre_operands: x.g: E
    // PCG: bb5[0] pre_operands: Unfreeze x.f
    // PCG: bb12[0] pre_operands: x: E
    let mut x = P { f: 0, g: 0 };
    let y = 0;
    let mut r = &x.f;
    let mut s = 0;
    let mut i = 0;
    while i < n {
        s += *r;
        if i == 3 {
            r = &y;
            x.f += 1;
        }
        x.g += 1;
        i += 1;
    }
    s + x.f
}

enum E {
    A(i32, i32),
    B(i32),
}

// An iteration lends a field of variant `A` mutably. The loop abstraction
// borrows that field; the loop head does not know the variant of `x`, so `x`
// holds nothing.
fn variant_field_lent(n: i32) -> i32 {
    // PCG_LIFETIME_DISPLAY: a 0 'a
    // PCG: bb0 -> bb1: Lend x to Loop(bb1): x@A.0 -> a↓'a
    // PCG: bb1[0] pre_operands: x: suspended E
    // ~PCG: bb1[0] pre_operands: x@A.1: E
    // PCG: bb5[0] pre_operands: x: E
    let mut x = E::A(0, 0);
    let mut y = 0;
    let mut a: &mut i32 = &mut y;
    let mut i = 0;
    while i < n {
        *a += 1;
        match x {
            E::A(ref mut p, _) => a = p,
            E::B(_) => a = &mut y,
        }
        i += 1;
    }
    *a
}

// An iteration lends a field of variant `A` for read, and another borrows
// variant `B` mutably (variants are disjoint). The loop head holds `x`
// frozen and packed, with only the layout of the borrowed field below it;
// borrowing `x@B.0` moves the freeze to `x@A`.
fn variant_field_shared_across_loop(n: i32, mut x: E) -> i32 {
    // PCG_LIFETIME_DISPLAY: a 0 'a
    // PCG: bb0 -> bb1: Add Edge Loop(bb1): x@A.0 -> a↓'a
    // PCG: bb1[0] pre_operands: x: R
    // PCG: bb1[0] pre_operands: x: suspended E
    // PCG: bb7[1] pre_operands: Refreeze x to x@A
    // ~PCG: bb7[1] pre_operands: Unfreeze x
    let y = 0;
    let mut a: &i32 = &y;
    let mut i = 0;
    let mut s = 0;
    while i < n {
        s += *a;
        match x {
            E::A(ref p, _) => a = p,
            E::B(ref mut q) => *q += 1,
        }
        i += 1;
    }
    s
}

// As above, behind a reference: the layout of the borrowed field is
// unpackings in the borrow PCG.
fn variant_field_shared_across_loop_through_ref(n: i32, x: &mut E) -> i32 {
    // PCG_LIFETIME_DISPLAY: a 0 'a
    // PCG: bb0 -> bb1: Add Edge Loop(bb1): (*x)@A.0 -> a↓'a
    // PCG: bb1[0] pre_operands: *x: R
    // PCG: bb1[0] pre_operands: *x: suspended E
    // PCG: bb7[1] pre_operands: Refreeze *x to (*x)@A
    // ~PCG: bb7[1] pre_operands: Unfreeze *x
    let y = 0;
    let mut a: &i32 = &y;
    let mut i = 0;
    let mut s = 0;
    while i < n {
        s += *a;
        match *x {
            E::A(ref p, _) => a = p,
            E::B(ref mut q) => *q += 1,
        }
        i += 1;
    }
    s
}

// As above, then `x` is overwritten: at the join after the match, the path
// that borrowed `x@B.0` packs its read copy of `x@B` into the frozen `x`, so
// no layout of `x@B` is left for the write to collapse.
fn variant_field_shared_then_overwritten(n: i32, mut x: E) -> i32 {
    // PCG_LIFETIME_DISPLAY: a 0 'a
    // PCG: bb9 -> bb10: Collapse(RepackCollapse { to: _2, capability: R, guide: Some(Downcast(Some("B"), 1)), _marker: PhantomData<&()> })
    // PCG: bb11[10] post_main: x: E
    let y = 0;
    let mut a: &i32 = &y;
    let mut i = 0;
    let mut s = 0;
    while i < n {
        s += *a;
        match x {
            E::A(ref p, _) => a = p,
            E::B(ref mut q) => *q += 1,
        }
        if i == 4 {
            a = &y;
            x = E::B(3);
        }
        i += 1;
    }
    s
}

// As `variant_field_shared_across_loop`, then `x` is moved: when the loop's
// loan of `x@A.0` ends, the layout below `x` is forgotten and `x` is
// unfrozen.
fn variant_field_shared_across_loop_then_moved(n: i32, x: E) -> E {
    // PCG: bb1[0] pre_operands: x: R
    // PCG: bb10[0] pre_operands: Unfreeze x
    let y = 0;
    let mut a: &i32 = &y;
    let mut i = 0;
    let mut s = 0;
    while i < n {
        s += *a;
        if let E::A(ref p, _) = x {
            a = p;
        }
        i += 1;
    }
    let _ = s;
    x
}

// As `variant_field_shared_across_loop`, for an element of an array: freezing
// `x` on the back edge records what the frozen `x[_]` records, not its read
// copies.
fn variant_field_shared_across_loop_in_array(n: i32, mut x: [E; 3], k: usize) -> i32 {
    // PCG: bb1[0] pre_operands: x: suspended E
    // PCG: bb12 -> bb1: Freeze x
    // ~PCG: bb12 -> bb1: Pack suspended x
    let y = 0;
    let mut a: &i32 = &y;
    let mut i = 0;
    let mut s = 0;
    while i < n {
        s += *a;
        match x[k] {
            E::A(ref p, _) => a = p,
            E::B(ref mut q) => *q += 1,
        }
        i += 1;
    }
    s
}

// Both fields of variant `A` are lent across the loop, and their loans end
// apart after it: the layout of `x@A` stays until the second ends, and then
// `x` is unfrozen.
fn variant_fields_shared_across_loop_end_apart(n: i32, mut x: E) -> i32 {
    // PCG_LIFETIME_DISPLAY: a 0 'a
    // PCG_LIFETIME_DISPLAY: b 0 'b
    // PCG: bb11[9] pre_operands: Remove Edge Loop(bb1): x@A.0 -> a↓'a under conditions bb2 -> bb11
    // ~PCG: bb11[9] pre_operands: Unfreeze x
    // PCG: bb11[12] pre_operands: Unfreeze x
    let y = 0;
    let mut a: &i32 = &y;
    let mut b: &i32 = &y;
    let mut i = 0;
    let mut s = 0;
    while i < n {
        s += *a + *b;
        if let E::A(ref p, ref q) = x {
            a = p;
            b = q;
        }
        i += 1;
    }
    let r = *a;
    let t = *b;
    x = E::B(r + t);
    s
}

// As `variant_field_shared_across_loop_in_array`, written after the loop:
// when the loop's loan ends, the layout below `x[_]` is forgotten and `x` is
// unfrozen.
fn variant_field_shared_across_loop_in_array_then_written(
    n: i32,
    mut x: [E; 3],
    k: usize,
) -> i32 {
    // PCG: bb13[0] pre_operands: Remove Edge Loop(bb1): x[_17]@A.0 -> a↓'a under conditions bb2 -> bb13
    // PCG: bb13[0] pre_operands: Unfreeze x
    // PCG_LIFETIME_DISPLAY: a 0 'a
    let y = 0;
    let mut a: &i32 = &y;
    let mut i = 0;
    let mut s = 0;
    while i < n {
        s += *a;
        match x[k] {
            E::A(ref p, _) => a = p,
            E::B(ref mut q) => *q += 1,
        }
        i += 1;
    }
    x[k] = E::B(1);
    s
}

// `x` is unpacked into variant `B` before the loop, which lends a field of
// variant `A`: the loop head has the layout of both variants. When the
// loans end, the layout of `x@A` is forgotten, so `x@A` can be unpacked.
fn variant_field_shared_across_loop_other_variant_read(n: i32, mut x: E) -> i32 {
    // PCG: bb12[12] pre_operands: Unfreeze x
    // PCG: bb15[1] pre_operands: x@A.0: E
    let y = 0;
    let E::B(ref b) = x else {
        return 0;
    };
    let mut a: &i32 = &y;
    let mut i = 0;
    while i < n {
        if let E::A(ref p, _) = x {
            a = p;
        }
        i += 1;
    }
    let t = *a + *b;
    if let E::A(ref mut q, _) = x {
        *q += 1;
    }
    t
}

// A field of variant `A` behind a reference is lent for read before the
// loop, which borrows variant `B` mutably: the freeze of `*x` moves to
// `(*x)@A`.
fn variant_field_shared_before_loop_through_ref(n: i32, x: &mut E) -> i32 {
    // PCG: bb10[1] pre_operands: Refreeze *x to (*x)@A
    // ~PCG: bb10[1] pre_operands: Unfreeze *x
    let y = 0;
    let mut a: &i32 = &y;
    if let E::A(ref p, _) = *x {
        a = p;
    }
    let mut i = 0;
    let mut s = 0;
    while i < n {
        s += *a;
        if let E::B(ref mut q) = *x {
            *q += 1;
        }
        i += 1;
    }
    s
}

// As `variant_field_shared_across_loop`, followed by a second loop that
// borrows variant `B` mutably. The first loop's loan of `x@A.0` blocks a part
// of the frozen `x`, so the second loop head keeps the layout `x -> x@A`
// instead of collapsing it, and the borrow of `x@B.0` moves the freeze to
// `x@A`.
fn variant_field_shared_across_loop_then_loop_mut_other(n: i32, mut x: E) -> i32 {
    // PCG: bb10[0] pre_operands: x: R
    // PCG: bb14[1] pre_operands: Refreeze x to x@A
    let y = 0;
    let mut a: &i32 = &y;
    let mut i = 0;
    while i < n {
        if let E::A(ref p, _) = x {
            a = p;
        }
        i += 1;
    }
    let mut j = 0;
    while j < n {
        if let E::B(ref mut q) = x {
            *q += 1;
        }
        j += 1;
    }
    *a
}

pub struct TrimmedFieldsWith<'a, F> {
    f: F,
    bytes: &'a [u8],
    chars: CharIndices<'a>,
}

// As `FieldsWith`, after a loop that skips the leading matches: the `for`
// loop borrows only `self.chars`; the lifetime it shares with `self.bytes`
// does not lend `*self`, so the loop can call `self.f`.
impl<'a, F: FnMut(char) -> bool> Iterator for TrimmedFieldsWith<'a, F> {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<&'a [u8]> {
        // PCG_LIFETIME_DISPLAY: iter 0 'iter
        // PCG: bb13[0] pre_operands: Loop(bb13): (*self).chars -> iter↓'iter under conditions bb3 -> bb6, bb8 -> bb10
        // ~PCG: bb13[0] pre_operands: Loop(bb13): *self -> iter↓'iter under conditions bb3 -> bb6, bb8 -> bb10
        // PCG: bb13[0] pre_operands: (*self).chars: suspended E
        // PCG: bb13[0] pre_operands: (*self).f: E
        // PCG: bb13[0] pre_operands: (*self).bytes: E
        let (start, mut end);
        loop {
            match self.chars.next() {
                None => return None,
                Some((s, e, ch)) => {
                    if !(self.f)(ch) {
                        start = s;
                        end = e;
                        break;
                    }
                }
            }
        }
        for (_, e, ch) in self.chars.by_ref() {
            if (self.f)(ch) {
                break;
            }
            end = e;
        }
        Some(&self.bytes[start..end])
    }
}

#[derive(Clone, Copy)]
pub struct Rules {
    a: u32,
    b: u32,
}

impl Rules {
    fn or(self, other: Rules) -> Rules {
        if self.a == 0 { other } else { self }
    }
}

pub struct Attrs {
    rules: Rules,
    name: u32,
}

impl Attrs {
    fn rules(&self) -> Rules {
        self.rules
    }
    fn rename(&mut self, r: Rules) {
        self.name = r.b;
    }
}

pub struct Field<'a> {
    ty: &'a u32,
    attrs: Attrs,
}

pub struct Variant<'a> {
    original: &'a u32,
    attrs: Attrs,
    fields: Vec<Field<'a>>,
}

pub enum Data<'a> {
    Enum(Vec<Variant<'a>>),
    Struct(u32, Vec<Field<'a>>),
}

// The inner loop lends `(*variant).fields` and reads `(*variant).attrs`:
// `*variant` keeps the R of the read unpacking above the lent field.
fn rename_variants<'a>(data: Data<'a>, attrs: &Attrs) -> Data<'a> {
    // PCG: bb16[0] pre_operands: variant: R
    // PCG: bb16[0] pre_operands: variant: suspended E
    // PCG: bb16[0] pre_operands: *variant: R
    // PCG: bb16[0] pre_operands: (*variant).attrs: R
    // ~PCG: bb16[0] pre_operands: (*variant).fields: R
    let mut data = data;
    match &mut data {
        Data::Enum(variants) => {
            for variant in variants {
                variant.attrs.rename(attrs.rules());
                for field in &mut variant.fields {
                    field.attrs.rename(variant.attrs.rules().or(attrs.rules()));
                }
            }
        }
        Data::Struct(_, fields) => {
            for field in fields {
                field.attrs.rename(attrs.rules());
            }
        }
    }
    data
}

// The two-phase borrow of `v` for `push` is reserved, not activated, at the
// loop head: `v` stays frozen through the loop until the activation.
fn reserved_across_loop(mut v: Vec<u32>) -> Vec<u32> {
    // PCG: bb1[0] pre_operands: v: R
    // PCG: bb1[0] pre_operands: v: suspended E
    // PCG: bb8[10] pre_operands: Activate two-phase borrow borrow: _3 = &mut  v
    v.push({
        let mut s = 0;
        let mut i = 0;
        while i < v.len() {
            s += v[i];
            i += 1;
        }
        s
    });
    v
}

enum Either<'a, 'b> {
    A(&'a u32),
    B(&'b mut u32),
}

// The loop lends `z` to the lifetime of the variant field that borrows it,
// not to the first lifetime of `x`: `z` comes back once that loan ends,
// while `a` keeps the other lifetime alive.
fn variant_blocker_lifetime<'a>(mut z: u32, w: &'a u32, n: u32) -> u32 {
    // PCG_LIFETIME_DISPLAY: x 1 'b
    // PCG: bb2[0] pre_operands: Loop(bb2): z -> x@B.0↓'b
    // PCG: bb2[0] pre_operands: z: suspended E
    // PCG: bb17[0] pre_operands: z: E
    let mut x: Either<'a, '_> = Either::B(&mut z);
    for _ in 0..n {
        if let Either::B(ref mut r) = x {
            **r += 1;
        }
    }
    let a: &u32 = if let Either::A(a) = x { a } else { w };
    let t = z;
    t + *a
}

// At the loop head `a` may borrow `x` and `b` may borrow `x.f` mutably:
// `x.f` is lent, and `x.g`, which only `a` borrows, is frozen.
fn shared_whole_mutable_part(c: bool) -> u32 {
    // PCG: bb1[0] pre_operands: x.f: suspended E
    // PCG: bb1[0] pre_operands: x.g: R
    // PCG: bb1[0] pre_operands: x.g: suspended E
    // PCG: bb9[0] pre_operands: x: E
    let mut x = P { f: 0, g: 0 };
    let mut y = 0;
    let z = P { f: 0, g: 0 };
    let mut s = 0;
    let mut a = &x;
    let mut b = &mut y;
    loop {
        s += a.g + x.g;
        *b += 1;
        if c {
            a = &z;
            b = &mut x.f;
        }
        if s > 10 {
            break;
        }
    }
    s
}

// The loop is on one branch between the reservation of the two-phase borrow
// for `push` and its activation: `*v` stays frozen through it.
fn reserved_across_loop_on_branch(v: &mut Vec<u32>, c: bool) {
    // PCG: bb2[0] pre_operands: *v: R
    // PCG: bb2[0] pre_operands: *v: suspended E
    // PCG: bb11[1] pre_operands: Activate two-phase borrow borrow: _4 = &mut  *v
    v.push(if c {
        let mut s = 0;
        let mut i = 0;
        while i < v.len() {
            s += v[i];
            i += 1;
        }
        s
    } else {
        0
    });
}

// The loop borrows an element at another index than the borrow before it,
// which may be the same element: the head records the value of both at
// `*xs`, and `xs` gets it back when the loans end.
fn element_borrowed_across_loop(xs: &mut [u32], c: bool) {
    // PCG: bb1 -> bb2: Pack suspended *xs
    // PCG: bb1 -> bb2: Add Edge {*xs} -> {(*xs)[_17]} (guide=Index(_17))
    // PCG: bb2[0] pre_operands: *xs: suspended E
    // PCG: bb5[0] pre_operands: xs: E
    let mut cur = &mut xs[0];
    let mut i = 1;
    while i < 3 {
        if c {
            cur = &mut xs[i];
        }
        i += 1;
    }
    *cur = 1;
}

// As above, for fields of elements: the field of the element before the loop
// that the loop does not borrow may be the field the loop borrows, so it is
// lent too.
fn element_field_borrowed_across_loop(v: &mut [(u32, u32)], n: usize) -> u32 {
    // PCG: bb1 -> bb2: Pack suspended *v
    // PCG: bb2[0] pre_operands: *v: suspended E
    // ~PCG: bb2[0] pre_operands: (*v)[_4].1: E
    let mut cur = &mut v[0].0;
    let mut i = 0;
    while i < n {
        if i == 2 {
            cur = &mut v[i].1;
        }
        i += 1;
    }
    *cur += 1;
    v[0].0
}

// As `element_borrowed_across_loop`, with the referents of the elements
// borrowed: what the element and its referent hold before the loop is packed
// into `*xs`, and neither element holds or records anything at the head.
fn referent_of_element_borrowed_across_loop(xs: &mut [&mut u32], c: bool) {
    // PCG: bb1 -> bb2: Pack suspended *xs
    // PCG: bb1 -> bb2: Add Edge {(*xs)[_17]} -> {*(*xs)[_17]}
    // PCG: bb2[0] pre_operands: *xs: suspended E
    // ~PCG: bb2[0] pre_operands: *(*xs)[_4]: suspended E
    // PCG: bb5[0] pre_operands: Remove Edge Loop(bb2): *(*xs)[_17] -> cur↓'?9 under conditions bb3 -> bb4, bb4 -> bb5 returning E to *xs
    let mut cur = &mut *xs[0];
    let mut i = 1;
    while i < 3 {
        if c {
            cur = &mut *xs[i];
        }
        i += 1;
    }
    *cur = 1;
}

// As above, in an array behind a reference.
fn referent_of_array_element_borrowed_across_loop<'a, 'b>(
    xs: &'b mut [&'a mut u32; 3],
    c: bool,
) {
    // PCG: bb1 -> bb2: Pack suspended *xs
    // PCG: bb2[0] pre_operands: *xs: suspended E
    let mut cur = &mut *xs[0];
    let mut i = 1;
    while i < 3 {
        if c {
            cur = &mut *xs[i];
        }
        i += 1;
    }
    *cur = 1;
}

// As above, in a `for` loop.
fn referent_of_element_borrowed_in_for_loop(xs: &mut [&mut u32], n: usize) {
    // PCG: bb2 -> bb3: Pack suspended *xs
    // PCG: bb3[0] pre_operands: *xs: suspended E
    let mut cur = &mut *xs[0];
    for i in 1..n {
        cur = &mut *xs[i];
    }
    *cur = 1;
}

// The elements are frozen apart by the pattern and the loop reads an element
// at another index: frozen elements and read copies may share an element, so
// nothing is packed, and the elements keep their records.
fn element_read_across_loop_beside_frozen_elements(
    mut arr: [String; 3],
    i: usize,
    c: bool,
) -> usize {
    // PCG: bb3[0] pre_operands: arr: suspended E
    // PCG: bb3[0] pre_operands: arr[ConstantIndex { offset: 0, min_length: 3, from_end: false }]: suspended E
    // ~PCG: bb2 -> bb3: Weaken suspended arr from E to R
    let [ref mut a, ref b, ..] = arr;
    a.push('z');
    let mut r = &arr[i];
    while c {
        r = &arr[2];
    }
    r.len() + b.len()
}

fn main() {}
