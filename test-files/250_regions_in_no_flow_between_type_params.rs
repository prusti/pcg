// Borrows inside a `T` never flow into a different type parameter `U`.

fn borrow_pair<T, U>(mut x: (T, U)) -> (T, U) {
    // PCG: bb0[1] post_main: Add Edge x↓RegionsIn(T) before bb0[1]:PostMain -> r↓RegionsIn(T)
    // PCG: bb0[1] post_main: Add Edge x↓RegionsIn(U) before bb0[1]:PostMain -> r↓RegionsIn(U)
    // ~PCG: bb0[1] post_main: Add Edge x↓RegionsIn(T) before bb0[1]:PostMain -> r↓RegionsIn(U)
    // ~PCG: bb0[1] post_main: Add Edge x↓RegionsIn(U) before bb0[1]:PostMain -> r↓RegionsIn(T)
    // ~PCG: bb0[1] post_main: Add Edge r↓RegionsIn(T) -> x↓RegionsIn(U) FUTURE
    // ~PCG: bb0[1] post_main: Add Edge r↓RegionsIn(U) -> x↓RegionsIn(T) FUTURE
    let r = &mut x;
    let _ = r;
    x
}

fn assign_pair<T, U>(x: &mut (T, U), y: (T, U)) {
    // PCG: bb0[1] post_main: Add Edge y before bb0[1]:PostOperands↓RegionsIn(T) -> _3↓RegionsIn(T)
    // PCG: bb0[1] post_main: Add Edge y before bb0[1]:PostOperands↓RegionsIn(U) -> _3↓RegionsIn(U)
    // ~PCG: bb0[1] post_main: Add Edge y before bb0[1]:PostOperands↓RegionsIn(T) -> _3↓RegionsIn(U)
    // ~PCG: bb0[1] post_main: Add Edge y before bb0[1]:PostOperands↓RegionsIn(U) -> _3↓RegionsIn(T)
    *x = y;
}

fn main() {}
