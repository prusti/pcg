enum List {
	Nil,
	Cons(u32, Box<List>),
}


fn all_zero(mut l : &mut List) {
	// ~PCG: bb1[0] post_main: Loop(bb1): l -> l↓'?6
	// PCG: bb1[0] post_main: Loop(bb1): Remote(_1)↓'?6 -> l↓'?6
	while let List::Cons(el, tl) = l {
		*el = 0;

		// PCG: bb4[7] post_main: l: E
		l = tl
	}
}

fn main() {}
