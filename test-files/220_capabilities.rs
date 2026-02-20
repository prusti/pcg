fn consume(p: String) {}
fn conditional_move(choice: bool) {
    let mut p = String::new();
    if choice {
        consume(p);
    } else {
        /* do nothing */
    }



}

fn borrow_expiry() {
    let mut p = String::new();
    let rp = &mut p;
    *rp = String::from("updated");
    assert!(p == "updated");
}

fn conditional_move_2(choice: bool) {
    let mut p = String::new();
    let mut p2 = String::new();
    let mut rp: &mut String;
    if true {
        consume(p);
        rp = &mut p2;
    } else {
        rp = &mut p;
    }



    *rp = String::from("updated");
    // rp expires


}

fn shared_borrow() {
    let mut pair = (String::new(), String::new());

    let r0 = &pair.0;


    let p1 = pair.1;



    let r1 = r0;


    // Borrows expire


}

fn shared_borrow_choice(choice: bool) {
    let mut pair1 = (String::new(), String::new());
    let mut pair2 = (String::new(), String::new());
    let r1 = &pair1.0;
    let p2: String;
    let r2: &(String, String);
    if choice {
        p2 = pair1.1;
        r2 = &pair2;
    } else {
        p2 = String::from("Hello");
        r2 = &pair1;
    }
    let r3 = r1;
    let r4 = r2;
}

fn examine(pair: &(String, String)) -> u32 { 0 }

fn mutate_str(str: &mut String, amt: u32) { }

struct Thing { value: String }

impl Thing {
    fn new() -> Self {
        Self { value: String::new() }
    }
    fn examine(&self) -> u32 { 0 }
    fn mutate(&mut self, amt: u32) { }
}

fn two_phase() {
    let mut pair = (String::new(), Thing::new());
    pair.1.mutate(pair.1.examine());
}
