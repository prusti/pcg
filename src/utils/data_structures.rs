//! The PCG's maps and sets. Their iteration order is deterministic: insertion
//! order, except that `swap_remove` moves the last element into the place of
//! the removed one. The iteration order of hash tables depends on the
//! addresses of interned compiler data, so with them the order of the actions
//! the PCG emits would vary between runs.
use crate::rustc_interface::data_structures::fx::{FxIndexMap, FxIndexSet};
pub(crate) type HashSet<T> = FxIndexSet<T>;
pub(crate) type HashMap<K, V> = FxIndexMap<K, V>;
