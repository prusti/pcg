type ByteStr = String;

/// Represents the path component of a URI
#[derive(Clone)]
pub struct PathAndQuery {
    pub data: ByteStr,
    pub query: u16,
}

const NONE: u16 = u16::MAX;

impl PathAndQuery {
    pub fn path(&self) -> &str {
        // The early return joins the path that read `*self` and froze `self`.
        // PCG: bb7 -> bb9: Freeze self
        // PCG: bb7 -> bb9: Add Edge {self} -> {*self} under conditions bb6 -> bb8 setting self: R, *self: R
        let ret = if self.query == NONE {
            &self.data[..]
        } else {
            &self.data[..self.query as usize]
        };

        if ret.is_empty() {
            return "/";
        }

        ret
    }
}

fn main() {
}
