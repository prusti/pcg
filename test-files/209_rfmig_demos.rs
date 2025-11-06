struct Pair { fst: String, snd: String }

fn rand_bool() -> bool {
    true
}

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

fn ex4_expiry(mut x: i32, mut y: i32, mut z: i32) {
    let r1 = &mut x;
    let r2 = if z > 5 {
        &mut *r1
    } else {
        x = 5;
        &mut y
    };
    *r2 = 5;
}

fn ex5_function_call(c: bool) {
    let mut x = 1;
    let mut y = 2;
    let r = choose(c, &mut x, &mut y);
    *r = 3;
}

fn ex6_loop<'a>(list: &'a mut List<i32>) -> Option<&'a mut i32> {
    let mut current = &mut *list;
    let mut prev = None;
    while let Some(next) = &mut current.tail {
        prev = Some(&mut current.head);
        current = &mut *next;
    }
    prev
}

fn ex7_path_sensitive(c: bool) {
    let mut x = 1;
    let mut y = 2;
    let r: &mut i32;
    if c {
        r = &mut x;
    } else {
        r = &mut y;
    };
    *r = 3;
}

fn g<T>(x1: &mut T, x2: &mut T){}

fn ex8_nested<'a>() {
    let mut x = 1;
    let mut y = 2;
    let mut r1 = &mut x;
    let mut r2 = &mut y;
    g(&mut r1, &mut r2);
    *r1 = 0;
    assert!(x == 0);
}

fn ex9_replace_head(mut list: List<String>, new_head: String, early_drop: bool) -> List<String> {
    if early_drop {
        drop(list.head);
    }
    list.head = new_head;
    list
}

fn choose<'a>(c: bool, x: &'a mut i32, y: &'a mut i32) -> &'a mut i32 {
    if c { x } else { y }
}


pub type Node<T> = Option<Box<List<T>>>;

struct List<T> {
    head: T,
    tail: Node<T>,
}


fn main() {
}
