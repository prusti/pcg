

fn main() {
	let mut x = 1;
	// PCG: bb1[1] pre_operands: _2: W
	// PCG: bb0[2] post_main: x: E
	x += 1;

	let y = &mut x;

	*y = 0;

	assert!(x == 0);
	// ~PCG: bb2[4] pre_main: Weaken RETURN from W to W
}
