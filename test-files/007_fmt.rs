// PCG_EXPECTED_FAILURE: frame <Ident as std::fmt::Debug>::fmt
// PCG_EXPECTED_FAILURE: label <Ident as std::fmt::Debug>::fmt
struct Ident {
    id: usize,
}

impl std::fmt::Debug for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Ident({:?})", self.id)
    }
}

fn main() {
}
