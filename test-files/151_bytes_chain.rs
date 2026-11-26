// PCG_EXPECTED_FAILURE: frame <Chain<T, U> as Buf>::chunks_vectored
use std::io::IoSlice;

struct Chain<T, U> {
    a: T,
    b: U,
}

trait Buf {
    fn chunks_vectored<'a>(&'a self, dst: &mut [IoSlice<'a>]) -> usize;
}

impl<T, U> Buf for Chain<T, U>
where
    T: Buf,
    U: Buf,
{
    fn chunks_vectored<'a>(&'a self, dst: &mut [IoSlice<'a>]) -> usize {
        let mut n = self.a.chunks_vectored(dst);
        n += self.b.chunks_vectored(&mut dst[n..]);
        n
    }
}

fn main() {}
