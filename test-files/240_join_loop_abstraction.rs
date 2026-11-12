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

// An iteration lends a field of variant `A`. The loop head does not know
// the variant of `x`, so it lends `x` whole.
fn variant_field_lent(n: i32) -> i32 {
    // PCG_LIFETIME_DISPLAY: a 0 'a
    // PCG: bb0 -> bb1: Lend x to Loop(bb1): x -> a↓'a
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

// The `for` loop borrows only `self.chars`; the lifetime it shares with
// `self.bytes` does not lend `*self`, so the loop can call `self.f`.
impl<'a, F: FnMut(char) -> bool> Iterator for FieldsWith<'a, F> {
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

fn main() {}
