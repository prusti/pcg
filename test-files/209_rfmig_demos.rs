struct Pair { fst: String, snd: String }

fn replace_fst(mut p: Pair, s: String) -> Pair {
    let tmp = p.fst;
    p.fst = s;
    p
}

fn borrow() {
   let mut x = 1;
   let y = &mut x;
   let z = &mut *y;
   *z = 5;
   *y = *y + 1;
   println!("x: {}", x); // prints 6
}

fn main() {
}
