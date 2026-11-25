// PCG_EXPECTED_FAILURE: frame foo
fn foo() {
    let mut a = 1;
    let mut b  = &mut a;
    let mut c = &mut b;
    let d = **c;
}

fn main(){

}
