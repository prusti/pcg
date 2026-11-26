// PCG_EXPECTED_FAILURE: frame foo
// PCG_EXPECTED_FAILURE: frame get

pub fn get(a: &&&usize) -> usize {
    ***a
}
fn foo(a: &&&usize) {
    let v = get(a);
}

fn main() {
}
