//! Regression tests for prusti issue-133 (gitlab): capability to a borrowed
//! local must be fully restored when the borrow expires.
//!
//! 1. Lending a place via `&mut` must not mark it uninitialised: on expiry
//!    the restored capability is computed from the initialisation state, so
//!    conflating "lent" with "moved out" restores `W` instead of `E`.
//!
//! 2. When two conditional variants of an edge become identical (here the
//!    `x = &mut a` borrow edge, whose labelled lifetime projections differ
//!    per match arm until they are unlabelled on expiry), their validity
//!    conditions must be joined. Dropping one variant's conditions makes
//!    the expiry (and the corresponding permission restoration) conditional
//!    on a single branch.
#![feature(box_patterns)]

pub struct U {
    f: u32,
}

pub struct ListNode {
    value: U,
    next: Option<Box<ListNode>>,
}

fn use_list_node(_x: &mut ListNode) {}
fn consume_u(_a: U) {}

pub fn whole_local_borrow_expiry(mut a: ListNode) {
    let x = &mut a;
    use_list_node(x);
    consume_u(a.value);
    // PCG: bb1[0] pre_operands: Restore capability E to a
    // PCG: bb1[0] post_operands: a: E
    // ~PCG: bb1[0] pre_operands: Restore capability W to a
    // ~PCG: bb1[0] post_operands: a: W
}

pub fn conditional_reborrow_expiry(mut a: ListNode) {
    let mut x = &mut a;
    let x = match x.next {
        Some(box ref mut node) => node,
        None => x,
    };
    use_list_node(x);
    consume_u(a.value);
    // The borrow of `a` was split into two conditional edge variants (one
    // per match arm); on expiry it must be removed under the union of their
    // conditions, not just one branch's.
    // PCG: bb6[0] pre_operands: Remove Edge borrow: x = &mut  a under conditions bb0 -> { bb3, bb2 }
    // PCG: bb6[0] pre_operands: Restore capability E to a
    // PCG: bb6[0] post_operands: a: E
    // ~PCG: bb6[0] pre_operands: Restore capability W to a
    // ~PCG: bb6[0] post_operands: a: W
    // ~PCG: bb6[0] pre_operands: Remove Edge borrow: x = &mut  a under conditions bb0 -> bb3
    // ~PCG: bb6[0] pre_operands: Remove Edge borrow: x = &mut  a under conditions bb0 -> bb2
}

fn main() {}
