struct Pair { fst: String, snd: String }

fn rand_bool() -> bool {
    true
}

fn ex1_replace_fst_cond(mut p: Pair, s: String) -> Pair {
    if rand_bool() {
        drop(p.fst);
    }
    // PCG: bb4 -> bb5: unpack p with capability E
    // PCG: bb4 -> bb5: Weaken(Weaken { place: _1.0, from: E, to: W, _marker: PhantomData<&()> })
    p.fst = s;
    p
}
