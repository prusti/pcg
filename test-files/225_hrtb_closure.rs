/// Test for functions with higher-ranked trait bound closures.
///
/// Calling a function that takes `impl FnMut(&T) -> bool` introduces a bound
/// region (`for<'_>`) from the HRTB. In the generalized outlives check, such
/// bound regions must be skipped when calling `sub_free_regions`, which asserts
/// both regions are free.
///
/// See: hashbrown's `RawTable::get` / `RawTable::find` pattern.
pub struct Table<T> {
    data: Vec<T>,
}

impl<T> Table<T> {
    pub fn find(&self, mut eq: impl FnMut(&T) -> bool) -> Option<&T> {
        self.data.iter().find(|x| eq(x))
    }

    pub fn get(&self, eq: impl FnMut(&T) -> bool) -> Option<&T> {
        self.find(eq)
    }
}
