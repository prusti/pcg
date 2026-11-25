// PCG_EXPECTED_FAILURE: frame foo
fn foo() {
    let x = 1;
    let y = &&&x;
    let a = ***y;
}

fn main(){

}
