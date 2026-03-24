fn main() {
    let mut abc = vec![1, 2, 3];
    let fst = &mut abc[0];
    *fst = 4;
    assert!(abc[0] == 4);
}
