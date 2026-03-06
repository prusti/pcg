fn unnest<'a, 'b, T>(x: &'a mut &'b mut T) -> &'a mut T {
	*x
}

fn rebor<'b, 'a : 'b, T>(x: &'a mut T) -> &'b mut T {
	x
	// PCG: bb0[3] pre_main: _2: W
}

fn main() {}
