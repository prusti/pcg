struct Pair { fst: String, snd: String }

fn ex1_replace_fst(mut p: Pair, s: String) -> Pair {
    let tmp = p.fst;
    p.fst = s;
    p
}

fn ex2_borrow() {
   let mut x = 1;
   let y = &mut x;
   let z = &mut *y;
   *z = 5;
   *y = *y + 1;
   println!("x: {}", x); // prints 6
}

fn ex3_distinct(x: &mut i32, y: &mut i32) {
    *x = 5;
    *y = 6;
    assert!(*x == 5);
}


fn ex4_path_sensitive(c: bool) {
    let mut x = 1;
    let mut y = 2;
    let r: &mut i32 = if c {
        &mut x
    } else {
        &mut y
    };
    *r = 3;
}

fn g<T>(x1: &mut T, x2: &mut T){}

fn ex5_nested<'a>() {
    let mut x = 1;
    let mut y = 2;
    let mut r1 = &mut x;
    let mut r2 = &mut y;
    g(&mut r1, &mut r2);
    *r1 = 0;
    assert!(x == 0);
}

fn choose<'a>(c: bool, x: &'a mut i32, y: &'a mut i32) -> &'a mut i32 {
    if c { x } else { y }
}

fn ex6_function_call(c: bool) {
    let mut x = 1;
    let mut y = 2;
    let r = choose(c, &mut x, &mut y);
    *r = 3;
}

fn main() {
}
