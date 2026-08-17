fn main() {
    let mut vec = vec![1, 2, 3];
    let mut x = &mut 0;
    for i in vec.iter_mut() {
        x = &mut *i;
    }
    // PCGTODO: bb7[0] post_main: Loop(bb7): (*_10) -> iter↓'?18
    // PCGTODO: bb7[0] post_main: Loop(bb7): (*_10) -> x↓'?12
    // PCG: bb7[0] post_main: Loop(bb7): _5 -> x↓'?12
    let y = *x;
}
