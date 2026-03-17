fn foo() {
    // bb0 {}
    'la: loop {
        'lb: loop {
            // bb1 {
                iter();
            // }
            // bb2 {
                if choice_inner() {
            // }
            // bb3 {
                continue; } // -> bb1
                break; // -> bb4
            // }
        }
        // bb4 {
            if choice_outer() {
        // }
        // bb5 {
            continue; } // -> bb1
            break; // -> bb6
        // }
    }
    // bb6 {}
}

fn choice_inner() -> bool { false }
fn choice_outer() -> bool { false }
fn iter() {}
fn main() {}