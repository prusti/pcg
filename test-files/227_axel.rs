fn fn_arg_reborrow(x: &i32) -> &i32 {
  let y = &(*x);
  y                       // MIR: actually `result = &(*y); return`
}

fn fn_arg_copy(x: &i32) -> &i32 {
  let y = x; // MIR: y = copy x
  y               // MIR: actually `result = &(*y); return`
}
