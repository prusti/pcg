trait MyTrait {
    type Output;
    fn call() -> Self::Output;
}

impl MyTrait for i32 {
    type Output = i32;
    fn call() -> i32 { 0 }
}

fn main() {
    let x = i32::call();
}
