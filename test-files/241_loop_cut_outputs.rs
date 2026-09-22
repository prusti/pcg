struct List<'a, 'b> {
    first: &'a mut i32,
    second: &'b mut i32,
    tail: Option<Box<List<'a, 'b>>>,
}

fn consume(mut list: List<'_, '_>) {
    // PCG_LIFETIME_DISPLAY: list 0 'first
    // PCG_LIFETIME_DISPLAY: list 1 'second
    // Cutting the paths through tail must preserve both sibling fields.
    // Each field remains connected only to its original remote projection.
    // PCG: bb1[0] pre_operands: Loop(bb1): Remote(_1)↓'first -> list.first before bb1[0]:PreOperands↓'first
    // PCG: bb1[0] pre_operands: Loop(bb1): Remote(_1)↓'second -> list.second before bb1[0]:PreOperands↓'second
    // ~PCG: bb1[0] pre_operands: Loop(bb1): Remote(_1)↓'first -> list.second before bb1[0]:PreOperands↓'second
    // ~PCG: bb1[0] pre_operands: Loop(bb1): Remote(_1)↓'second -> list.first before bb1[0]:PreOperands↓'first
    while let Some(tail) = list.tail {
        list = *tail;
    }
}

fn main() {}
