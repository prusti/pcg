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
    // Preserve the sibling field when the loop abstracts the path through tail.
    // PCG: bb1[0] pre_operands: Loop(bb1): Remote(_1)↓'a -> list.head before bb1[0]:PreOperands↓'a
    // PCG: bb1[0] pre_operands: list.tail@Some before bb1[0]:PreOperands↓'a -> list.tail before bb1[0]:PreOperands↓'a
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
    // PCG: bb7[0] pre_operands: Loop(bb7): Remote(_1)↓'list -> list.head before bb7[0]:PreOperands↓'list
    // PCG: bb7[0] pre_operands: Loop(bb7): Remote(_2)↓'other -> list.head before bb7[0]:PreOperands↓'list
    // Collapsing one child must preserve the path from the remote projections to tail.
    // PCG: bb7[0] pre_operands: Loop(bb7): Remote(_1)↓'list -> list.tail@Some.0 before bb7[0]:PreOperands↓'list
    // PCG: bb7[0] pre_operands: Loop(bb7): Remote(_2)↓'other -> list.tail@Some.0 before bb7[0]:PreOperands↓'list
    // PCG: bb7[0] pre_operands: list.tail@Some.0 before bb7[0]:PreOperands↓'list -> list.tail@Some before bb7[0]:PreOperands↓'list
    // PCG: bb7[0] pre_operands: list.tail@Some before bb7[0]:PreOperands↓'list -> list.tail before bb7[0]:PreOperands↓'list
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

fn main() {}
