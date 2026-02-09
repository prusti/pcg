use std::time::Instant;
fn run_expensive_calculation(){}
fn main() {
  let start = Instant::now();
  run_expensive_calculation();
  let elapsed = start.elapsed();
  // Currently this desugars into a function call that uses unsafe ptrs with a
  // nested lifetime and therefore isn't supported by PCG.
  // println!("Elapsed: {}s", elapsed.as_secs());
}
