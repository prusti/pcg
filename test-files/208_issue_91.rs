#![feature(arbitrary_self_types)]
use std::cell::Cell;
use std::ops::Deref;

struct TypedArena<T> {
    end: Cell<*mut T>,
}

struct ResolverArenas<'ra> {
    imports: &'ra TypedArena<&'ra ()>,
}

struct Resolver<'ra, 'tcx> {
    tcx: &'tcx (),
    arenas: &'ra ResolverArenas<'ra>,
}
type CmResolver<'r, 'ra, 'tcx> = RefOrMut<'r, Resolver<'ra, 'tcx>>;

struct RefOrMut<'a, T> {
    p: &'a mut T,
}

impl<'a, T> Deref for RefOrMut<'a, T> {
    type Target = T;
    fn deref(&self) -> &T {
        todo!()
    }
}

impl<'a, T> RefOrMut<'a, T> {
    pub fn reborrow(&mut self) -> RefOrMut<'_, T> {
        todo!()
    }
}

impl<'ra, 'tcx> Resolver<'ra, 'tcx> {
    fn import(&self, _import: &'ra ()) -> &'ra () {
        todo!()
    }
    fn per_ns_cm<'r>(self: CmResolver<'r, 'ra, 'tcx>, _f: impl FnMut(CmResolver<'_, 'ra, 'tcx>)) {}
    fn resolve_import<'r>(self: CmResolver<'r, 'ra, 'tcx>, import: &'ra ()) {
        // PCG_LIFETIME_DISPLAY: self 0 'r
        // PCG_LIFETIME_DISPLAY: self 1 'ra
        // PCG_LIFETIME_DISPLAY: self 2 'tcx
        // for some reason the borrow checker thinks that 'ra should outlive 'tcx
        // but this does not happen with bare &mut Resolver<'ra, 'tcx>
        self.per_ns_cm(|mut this| {
            let _ = this.reborrow().import(import);
        });
    }
}

fn main(){}
