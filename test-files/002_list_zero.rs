// PCG_EXPECTED_FAILURE: label all_zero
enum List {
	Nil,
	Cons(u32, Box<List>),
}


fn all_zero(mut l : &mut List) {
	while let List::Cons(el, tl) = l {
		*el = 0;

		// PCG: bb4[7] post_main: l: E
		l = tl
	}
}

fn main() {}
