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
    // PCG: bb1[0] pre_operands: Remove Edge borrow: x = &mut  a returning E to a
    // PCG: bb1[0] post_operands: a: E
    // ~PCG: bb1[0] pre_operands: Remove Edge borrow: x = &mut  a returning W to a
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
    // PCG: bb6[0] pre_operands: Remove Edge borrow: x = &mut  a under conditions bb0 -> { bb3, bb2 } returning E to a
    // PCG: bb6[0] post_operands: a: E
    // ~PCG: bb6[0] pre_operands: Remove Edge borrow: x = &mut  a under conditions bb0 -> { bb3, bb2 } returning W to a
    // ~PCG: bb6[0] post_operands: a: W
    // ~PCG: bb6[0] pre_operands: Remove Edge borrow: x = &mut  a under conditions bb0 -> bb3
    // ~PCG: bb6[0] pre_operands: Remove Edge borrow: x = &mut  a under conditions bb0 -> bb2
    // At the join, `(*x).value` is lent to the reborrow of `*x` made in the
    // other arm.
    // PCG: bb4 -> bb5: Lend (*x).value to borrow: x = &mut  *x under conditions bb0 -> bb3
}

fn main() {}

pub struct Inner<T>(Option<T>);
impl<T> Inner<T> {
    fn reset(&mut self) {}
}
pub struct Outer<T>(Inner<T>);
impl<T> Unpin for Inner<T> {}

/// `Pin::new(&mut s.0)` reborrows `s` for `deref_mut`; the borrow checker ends
/// that borrow once `take` returns, although the regions of `T` in the result
/// flow from it. The borrow of `s` is removed there and gives `s` back, so
/// that `s.0.reset()` can borrow `s` again.
pub fn borrow_ends_while_type_regions_flow<T>(mut s: std::pin::Pin<&mut Outer<T>>) -> Option<T> {
    // PCG: bb4[0] pre_operands: Remove Edge borrow: _9 before bb0[9]:PostOperands <before bb0[9]:PostMain> = &mut  s returning E to s
    // PCG: bb7[6] pre_operands: s: E
    match std::pin::Pin::new(&mut s.0).0.take() {
        None => None,
        Some(item) => {
            s.0.reset();
            Some(item)
        }
    }
}

/// As above in a loop: the borrow of `(*x).0` is removed in the iteration
/// that takes it, so the loop head gets `(*x).0` back.
pub fn borrow_ends_in_loop_while_type_regions_flow<T>(x: &mut Outer<T>, n: u32) -> Option<T> {
    // PCG: bb6[0] pre_operands: Remove Edge borrow: _15 before bb3[9]:PostOperands <before bb3[9]:PostMain> = &mut  (*x).0 under conditions bb2 -> bb3 returning E to (*x).0
    // PCG: bb1 loop invariant: x: E
    let mut v = None;
    let mut i = 0;
    while i < n {
        v = std::pin::Pin::new(&mut x.0).0.take();
        i += 1;
    }
    v
}

/// As above for an element of a slice, which `x[i].reset()` then uses.
pub fn borrow_of_element_ends_while_type_regions_flow<T>(x: &mut [Inner<T>], i: usize) -> Option<T> {
    // PCG: bb4[0] pre_operands: Remove Edge borrow: _8 before bb1[1]:PostOperands <before bb1[1]:PostMain> = &mut  (*x)[_9] returning E to (*x)[_9]
    let v = std::pin::Pin::new(&mut x[i]).0.take();
    x[i].reset();
    v
}

/// As above through a raw pointer: the borrow checker does not track the
/// borrow of `*p`, so the PCG keeps it while its result lives.
pub unsafe fn untracked_borrow_kept<T>(p: *mut Inner<T>) -> Option<T> {
    // PCG: bb0[7] pre_operands: *p: suspended E
    // ~PCG: bb0[7] pre_operands: Remove Edge borrow: _7 = &mut  *p returning E to *p
    unsafe {
        let v = std::pin::Pin::new(&mut *p).0.take();
        (*p).reset();
        v
    }
}
