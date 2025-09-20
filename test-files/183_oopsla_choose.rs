fn choose<'a, T>(c: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T {
    if c {
        x
    } else {
        y
    }
}

fn f<'a>(ra: &'a mut u32, rb: &'a mut u32) {
    let res = choose(true, ra, rb);
    // PCG: bb1[1] post_main: call choose at bb0[5]: [_4 before bb0[5]:PostOperands↓'?8 before bb0[5]:PostMain, _5 before bb0[5]:PostOperands↓'?9 before bb0[5]:PostMain] -> [res↓'?7]
    *res = 10;
}

fn main() {}
