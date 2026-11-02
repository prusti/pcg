struct Cache;
pub struct ByteClasses([u8; 256]);
pub struct Unit;

pub struct ByteClassRepresentatives<'a> {
    classes: &'a ByteClasses,
    cur_byte: usize,
    end_byte: Option<usize>,
    last_class: Option<u8>,
}


impl<'a> Iterator for ByteClassRepresentatives<'a> {
    type Item = Unit;

    fn next(&mut self) -> Option<Unit> {
        unimplemented!()
    }
}

impl ByteClasses {
    pub fn representatives<R: core::ops::RangeBounds<u8>>(
        &self,
        range: R,
    ) -> ByteClassRepresentatives<'_> {
        unimplemented!()
    }
}

struct DFA {
    classes: ByteClasses
}
struct Lazy<'i, 'c> {
    dfa: &'i DFA,
    cache: &'c mut Cache,
}

#[derive(Copy, Clone)]
pub struct LazyStateID(u32);

impl<'i, 'c> Lazy<'i, 'c> {

    fn set_transition(
        &mut self,
        from: LazyStateID,
        unit: Unit,
        to: LazyStateID,
    ) {
        unimplemented!()
    }

    fn set_all_transitions(&mut self, from: LazyStateID, to: LazyStateID) {
        // The loop borrows `*self` mutably while the iterator borrows the
        // classes behind the shared reference `self.dfa`.
        // PCG: bb2 -> bb3: Label place *(*self).dfa (Detach)
        // PCG: bb2 -> bb3: Remove Edge {(*self).dfa} -> {*(*self).dfa loop bb3}
        // PCG: bb2 -> bb3: Remove Edge {*self} -> {(*self).dfa, (*self).cache}
        // PCG: bb2 -> bb3: Unfreeze self
        // ~PCG: bb2 -> bb3: Weaken *(*self).dfa from R to None
        for unit in self.dfa.classes.representatives(..) {
            self.set_transition(from, unit, to);
        }
    }
}

fn main(){}
