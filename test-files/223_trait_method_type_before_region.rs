/// Regression test for a panic in `normalized_to_identity` when calling a trait
/// method whose identity generic args have type parameters before lifetime
/// parameters (e.g. `[Self/#0, 'a/#1]`).
///
/// The bug was that region indexing used `.regions().position(...)` which gives
/// the index among only regions, but then used `region_at(index)` which indexes
/// into all generic args. When a type param like `Self` precedes the region in
/// the identity substs, these indices disagree and the lookup panics.

trait Accessor<'a> {
    fn access(&self) -> &'a str;
}

struct Data<'a> {
    value: &'a str,
}

impl<'a> Accessor<'a> for Data<'a> {
    fn access(&self) -> &'a str {
        self.value
    }
}

fn use_accessor<'a>(d: &Data<'a>) -> &'a str {
    d.access()
}

fn caller() {
    let s = String::from("hello");
    let d = Data { value: &s };
    let r = use_accessor(&d);
    assert_eq!(r, "hello");
}

fn main() {
    caller();
}
