use std::rc::Rc;

use crate::pcg::PcgArena;

pub(crate) type PcgArenaRef<'a, T> = Rc<T, PcgArena<'a>>;
