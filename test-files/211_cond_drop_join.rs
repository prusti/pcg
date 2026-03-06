struct Pair { fst: String, snd: String }

fn rand_bool() -> bool {
    true
}

fn ex1_replace_fst_cond(mut p: Pair, s: String) -> Pair {
    if rand_bool() {
        drop(p.fst);
    }
    // PCG: bb4 -> bb5: unpack p with capability Real
    // PCG: bb4 -> bb5: Weaken p.fst from D to U
    p.fst = s;
    p
}
