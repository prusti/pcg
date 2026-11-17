// Moving `from` cuts the delegation of its borrow to `*ptr`: `ptr` no longer
// gives access to `from`, but its own value is still valid, so this safe
// function can still copy it.
pub fn raw_pointer_copied_after_cut(from: String) -> *const String {
    // PCG: bb0[8] pre_operands: Remove Edge {(*_3) before bb0[5]:PreMain} -=-> {*ptr}
    // PCG: bb1[2] pre_operands: ptr: E
    let ptr = &from as *const String;
    drop(from);
    ptr
}
