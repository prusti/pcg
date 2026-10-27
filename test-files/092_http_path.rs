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
        // The path that read `*self` joins the early return, where `self` is
        // dead: `self` is unfrozen and its value given up.
        // PCG: bb8 -> bb9: Unfreeze self
        // PCG: bb8 -> bb9: Weaken self from E to W
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
