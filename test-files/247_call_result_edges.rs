// Edges from the arguments of a call into its result and into what its
// arguments point to after the call. Only regions that may flow into these
// according to the callee's signature get an edge.

// The result of `take` cannot hold the local `&mut v` borrow, so it does not
// block `v`, which must be available again for the implicit `drop(v)`.
fn take<T>(v: &mut Vec<T>) -> T {
    unimplemented!()
}

// The caller chooses `T`, so a value of type `T` cannot hold a borrow created
// in the body.
fn generic<T>(mut v: Vec<T>) -> T {
    // PCG: bb0[4] post_main: Add Edge call take at bb0[4]: [_2 before bb0[4]:PostOperands↓RegionsIn(T) before bb0[4]:PostMain] -> [RETURN↓RegionsIn(T), _2 before bb0[4]:PostOperands↓RegionsIn(T) after bb0]
    // PCG: bb1[2] pre_operands: v: E
    take(&mut v)
}

// The result has type `&'static i32`, so it cannot hold the borrow even though
// `take` returns its type parameter `T`.
fn static_ref(mut v: Vec<&'static i32>) -> &'static i32 {
    // PCG: bb0[5] post_main: Add Edge call take at bb0[5]: [_3 before bb0[5]:PostOperands↓'?10 before bb0[5]:PostMain] -> [_2↓'?8, _3 before bb0[5]:PostOperands↓'?10 after bb0]
    // PCG: bb1[2] pre_operands: v: E
    take(&mut v)
}

fn id<T>(x: T) -> T {
    x
}

// Both references map to `RegionsIn(T)` in the signature of `id`, but the
// borrows under `'a` and `'b` do not flow into each other.
fn id_pair<'a, 'b>(x: (&'a mut i32, &'b mut i32)) -> (&'a mut i32, &'b mut i32) {
    // PCG: bb0[2] post_main: Add Edge call id at bb0[2]: _2 before bb0[2]:PostOperands↓'?10 before bb0[2]:PostMain -> RETURN↓'?6
    // PCG: bb0[2] post_main: Add Edge call id at bb0[2]: _2 before bb0[2]:PostOperands↓'?11 before bb0[2]:PostMain -> RETURN↓'?7
    // ~PCG: bb0[2] post_main: Add Edge call id at bb0[2]: _2 before bb0[2]:PostOperands↓'?10 before bb0[2]:PostMain -> RETURN↓'?7
    // ~PCG: bb0[2] post_main: Add Edge call id at bb0[2]: _2 before bb0[2]:PostOperands↓'?11 before bb0[2]:PostMain -> RETURN↓'?6
    id(x)
}

fn first<'a, 'b>(x: &'a u32, _y: std::cell::Cell<&'b u32>) -> &'a u32 {
    x
}

// `first`'s signature does not let `'b` flow into `'a`. The borrow checker
// alone would allow it, since `Cell` forces both to `'c` at this call.
fn first_with_cell<'c>(x: &'c u32, y: std::cell::Cell<&'c u32>) -> &'c u32 {
    // PCG: bb0[5] post_main: Add Edge call first at bb0[5]: _4 before bb0[5]:PostOperands↓'?9 before bb0[5]:PostMain -> _3↓'?8
    // ~PCG: bb0[5] post_main: Add Edge call first at bb0[5]: _5 before bb0[5]:PostOperands↓'?10 before bb0[5]:PostMain -> _3↓'?8
    // ~PCG: bb0[5] post_main: Add Edge call first at bb0[5]: [_4 before bb0[5]:PostOperands↓'?9 before bb0[5]:PostMain, _5 before bb0[5]:PostOperands↓'?10 before bb0[5]:PostMain] -> [_3↓'?8]
    first(x, y)
}

fn store_opt<'a, 'b>(o: Option<&'a mut Vec<&'b String>>, x: &'b String) {
    if let Some(v) = o {
        v.push(x);
    }
}

// `'b` is invariant in `Option<&'a mut Vec<&'b String>>`, so `store_opt` may
// store `x` into the vector that `o` points to: `s` stays borrowed until the
// last use of `v`.
fn store_through_option(s: String) -> usize {
    let mut v: Vec<&String> = vec![];
    // PCG: bb1[14] post_main: Add Edge call store_opt at bb1[14]: [_7 before bb1[14]:PostOperands↓'?18 before bb1[14]:PostMain, _4 before bb1[14]:PostOperands↓'?13 before bb1[14]:PostMain] -> [_4 before bb1[14]:PostOperands↓'?13 after bb1]
    store_opt(Some(&mut v), &s);
    v.len()
}

trait Sink<'b> {
    fn put(&mut self, x: &'b String);
}

impl<'b> Sink<'b> for Vec<&'b String> {
    fn put(&mut self, x: &'b String) {
        self.push(x)
    }
}

impl<'b, 'x> Sink<'b> for (Vec<&'b String>, &'x u8) {
    fn put(&mut self, x: &'b String) {
        self.0.push(x)
    }
}

impl<'b, T: Sink<'b>> Sink<'b> for Box<T> {
    fn put(&mut self, x: &'b String) {
        (**self).put(x)
    }
}

// Proving `Vec<&String>: Sink<'_>` with the impl above equates the regions of
// the vector and of `x`: `put` may store `x` into the vector.
fn put_through_trait(s: String) -> usize {
    let mut v: Vec<&String> = vec![];
    // PCG: bb1[11] post_main: Add Edge call Sink::put at bb1[11]: [_4 before bb1[11]:PostOperands↓'?13 before bb1[11]:PostMain, _6 before bb1[11]:PostOperands↓'?16 before bb1[11]:PostMain] -> [_4 before bb1[11]:PostOperands↓'?13 after bb1]
    Sink::put(&mut v, &s);
    v.len()
}

// The impl for the pair relates the trait's `'b` to the vector's region only,
// not to the region of the `&u8`.
fn put_into_pair(s: String, byte: u8) -> usize {
    let mut v: (Vec<&String>, &u8) = (vec![], &byte);
    // PCG: bb2[13] post_main: Add Edge call Sink::put at bb2[13]: [_10 before bb2[13]:PostOperands↓'?26 before bb2[13]:PostMain, _8 before bb2[13]:PostOperands↓'?21 before bb2[13]:PostMain] -> [_8 before bb2[13]:PostOperands↓'?21 after bb2]
    // PCG: bb2[13] post_main: Add Edge call Sink::put at bb2[13]: _8 before bb2[13]:PostOperands↓'?22 before bb2[13]:PostMain -> _8 before bb2[13]:PostOperands↓'?22 after bb2
    Sink::put(&mut v, &s);
    v.0.len()
}

// The impl for `Box<T>` proves its bound with the impl for the vector.
fn put_through_box(s: String) -> usize {
    let mut v: Box<Vec<&String>> = Box::new(vec![]);
    // PCG: bb2[12] post_main: Add Edge call Sink::put at bb2[12]: [_5 before bb2[12]:PostOperands↓'?15 before bb2[12]:PostMain, _7 before bb2[12]:PostOperands↓'?18 before bb2[12]:PostMain] -> [_5 before bb2[12]:PostOperands↓'?15 after bb2]
    Sink::put(&mut v, &s);
    v.len()
}

// The object type `dyn Sink<'b>` may hold borrows of `'b`.
fn put_through_dyn(s: String) -> usize {
    let mut v: Vec<&String> = vec![];
    {
        let d: &mut dyn Sink = &mut v;
        // PCG: bb1[20] post_main: Add Edge call Sink::put at bb1[20]: [_9 before bb1[20]:PostOperands↓'?27 before bb1[20]:PostMain, _8 before bb1[20]:PostOperands↓'?25 before bb1[20]:PostMain] -> [_8 before bb1[20]:PostOperands↓'?25 after bb1]
        d.put(&s);
    }
    v.len()
}

// The bound `T: Sink<'c>` lets `put` store `x` into the part `T['c]` of `*t`.
fn put_generic<'c, T: Sink<'c>>(t: &mut T, x: &'c String) {
    // PCG: bb0[4] post_main: Add Edge call Sink::put at bb0[4]: [_4 before bb0[4]:PostOperands↓'?9 before bb0[4]:PostMain, _3 before bb0[4]:PostOperands↓T[ReEarlyParam('c/#0)] before bb0[4]:PostMain] -> [_3 before bb0[4]:PostOperands↓T[ReEarlyParam('c/#0)] after bb0]
    t.put(x)
}

// `Self: Extend<A>` and `I: IntoIterator<Item = A>` with the impls for `Vec`
// and `Option` equate the regions of the vector and of the option's item.
fn extend_vec(s: String) -> usize {
    let mut v: Vec<&String> = vec![];
    // PCG: bb1[10] post_main: Add Edge call std::iter::Extend::extend at bb1[10]: [_5 before bb1[10]:PostOperands↓'?14 before bb1[10]:PostMain, _4 before bb1[10]:PostOperands↓'?13 before bb1[10]:PostMain] -> [_4 before bb1[10]:PostOperands↓'?13 after bb1]
    v.extend(Some(&s));
    v.len()
}

// The closure stores its argument into the vector it captures, which its body
// requires of the regions of its type.
fn push_through_closure(s: String) -> usize {
    let mut v: Vec<&String> = vec![];
    {
        let mut f = |x| v.push(x);
        // PCG: bb1[18] post_main: Add Edge call std::ops::FnMut::call_mut at bb1[18]: [_8 before bb1[18]:PostOperands↓'?26 before bb1[18]:PostMain, _7 before bb1[18]:PostOperands↓'?25 before bb1[18]:PostMain, _7 before bb1[18]:PostOperands↓'?24 before bb1[18]:PostMain] -> [_7 before bb1[18]:PostOperands↓'?24 after bb1, _7 before bb1[18]:PostOperands↓'?25 after bb1]
        f(&s);
    }
    v.len()
}

// `map` passes the `&String` to the closure, which returns it.
fn map_identity(s: String) -> usize {
    // PCG: bb0[8] post_main: Add Edge call std::option::Option::<T>::map at bb0[8]: _3 before bb0[8]:PostOperands↓'?13 before bb0[8]:PostMain -> r↓'?12
    let r = Some(&s).map(|r| r);
    r.unwrap().len()
}

fn wrap<'a>(x: &'a String) -> impl Iterator<Item = &'a String> + 'a {
    std::iter::once(x)
}

// The value of the opaque result may hold borrows of `'a`, in the part of it
// that its argument `'a` names.
fn wrap_ref(s: String) -> usize {
    // PCG: bb0[5] post_main: Add Edge call wrap at bb0[5]: _3 before bb0[5]:PostOperands↓'?6 before bb0[5]:PostMain -> it↓impl std::iter::Iterator<Item = &std::string::String> + '_[RegionVid('?5)]
    let it = wrap(&s);
    it.count()
}

fn second<'a>(p: (&'a u32, &'a u32)) -> &'a u32 {
    p.1
}

// Both references of the pair have the region `'a` in the signature, so both
// may flow into the result.
fn second_of_pair(a: u32, b: u32) -> u32 {
    // PCG: bb0[13] post_main: Add Edge call second at bb0[13]: [_4 before bb0[13]:PostOperands↓'?7 before bb0[13]:PostMain, _4 before bb0[13]:PostOperands↓'?8 before bb0[13]:PostMain] -> [r↓'?6]
    let r = second((&a, &b));
    *r
}

fn print_byte(_x: &u8) {}

fn take_fn_ptr<'a>(_f: fn(&'a u8)) {}

// A higher-ranked function pointer is passed for a parameter of a type with a
// free region. The region bound in the argument's type flows nowhere.
fn pass_higher_ranked() {
    let f: for<'x> fn(&'x u8) = print_byte;
    take_fn_ptr(f);
}

unsafe extern "C" {
    fn printf(format: *const u8, ...) -> i32;
}

// The arguments beyond the parameters of a C-variadic function flow nowhere.
fn call_variadic(format: *const u8) {
    unsafe {
        printf(format, 1i32);
    }
}

trait Tr<'a> {
    type Out;
}

// The where clause on the alias type gives it a part for `'a`, into which
// `put` may store `s`, in the body as in the signature.
fn put_into_alias<'a, T: Tr<'a>>(x: &mut <T as Tr<'a>>::Out, s: &'a String)
where
    <T as Tr<'a>>::Out: Sink<'a>,
{
    // PCG: bb0[4] post_main: Add Edge call Sink::put at bb0[4]: [_4 before bb0[4]:PostOperands↓'?13 before bb0[4]:PostMain, _3 before bb0[4]:PostOperands↓<T as Tr<'_>>::Out[ReEarlyParam('a/#0)] before bb0[4]:PostMain, _3 before bb0[4]:PostOperands↓<T as Tr<'_>>::Out[RegionVid('?12)] before bb0[4]:PostMain] -> [_3 before bb0[4]:PostOperands↓<T as Tr<'_>>::Out[ReEarlyParam('a/#0)] after bb0, _3 before bb0[4]:PostOperands↓<T as Tr<'_>>::Out[RegionVid('?12)] after bb0]
    // PCG: bb0[4] post_main: Add Edge call Sink::put at bb0[4]: _3 before bb0[4]:PostOperands↓<T as Tr<'_>>::Out[RegionsIn(T)] before bb0[4]:PostMain -> _3 before bb0[4]:PostOperands↓<T as Tr<'_>>::Out[RegionsIn(T)] after bb0
    x.put(s)
}

// The items of `I::IntoIter` are in its part for `'a`, which `I['a]` flows
// into; the rest of `I` flows into its part for `RegionsIn(I)`. So only
// `I['a]` flows into the result, as the signature says.
fn first_item<'a, I: IntoIterator<Item = &'a u32>>(i: I) -> Option<&'a u32> {
    // PCG: bb0[4] post_main: Add Edge call std::iter::IntoIterator::into_iter at bb0[4]: [_4 before bb0[4]:PostOperands↓I[ReEarlyParam('a/#0)] before bb0[4]:PostMain] -> [_3↓<I as std::iter::IntoIterator>::IntoIter[ReEarlyParam('a/#0)], _4 before bb0[4]:PostOperands↓I[ReEarlyParam('a/#0)] after bb0]
    // PCG: bb1[2] post_main: Add Edge call std::iter::Iterator::next at bb1[2]: _2 before bb1[2]:PostOperands↓<I as std::iter::IntoIterator>::IntoIter[RegionsIn(I)] before bb1[2]:PostMain -> _2 before bb1[2]:PostOperands↓<I as std::iter::IntoIterator>::IntoIter[RegionsIn(I)] after bb1
    // PCG: bb1[2] post_main: Add Edge call std::iter::Iterator::next at bb1[2]: [_2 before bb1[2]:PostOperands↓<I as std::iter::IntoIterator>::IntoIter[ReEarlyParam('a/#0)] before bb1[2]:PostMain] -> [_2 before bb1[2]:PostOperands↓<I as std::iter::IntoIterator>::IntoIter[ReEarlyParam('a/#0)] after bb1, RETURN↓'?4]
    i.into_iter().next()
}

fn main() {}
