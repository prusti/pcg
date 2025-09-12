struct T1 {
    f: u32,
    g: u32,
    h: u32,
}

struct T2 {
    f: T1,
    g: T1,
    h: T1,
}

struct T3 {
    f: T1,
    g: T2,
    h: T2,
}


struct S1 {
    f: T1,
}

struct S2 {
    f: S1,
}

fn _test4(b: bool, mut x: S2, y: T1) {
    if b {
        let z = x.f.f;
    }
    // PCG: bb3[4] pre_main: Expand(RepackExpand { from: _2, guide: None, capability: W })
    x.f.f = y;
}

fn main() {}
