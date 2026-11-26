// PCG_EXPECTED_FAILURE: frame f
// PCG_EXPECTED_FAILURE: label f
fn main() {
}

fn f(x_orig: &mut [u8]) {
    let x = x_orig;
    for c in x.chunks(2) {
        println!("{:?}", c);
    }
}
