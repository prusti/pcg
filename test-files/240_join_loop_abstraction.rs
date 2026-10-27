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

fn main() {}
