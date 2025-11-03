struct Pair { fst: String, snd: String }

fn borrow() {
   let mut x = 1;
   let y = &mut x;
   let z = &mut *y;
   *z = 5;
   *y = *y + 1;
   println!("x: {}", x); // prints 6
}

fn replace_fst(mut p: Pair, s: String) -> Pair {
    let tmp = p.fst;
    p.fst = s;
    p
}

fn path_sensitive(c: bool) {
    let x = 1;
    let y = 2;
    let r: &mut i32 = if c {
        y = &mut x;
    } else {
        y = &mut x;
    };
    *r = 3;
}


fn main() {
}
