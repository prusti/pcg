struct Pair { fst: String, snd: String }

fn replace_fst(mut p: Pair, s: String) -> Pair {
    let tmp = p.fst;
    p.fst = s;
    p
}

fn main() {
}
