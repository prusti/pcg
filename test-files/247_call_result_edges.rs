// Edges from the arguments of a call into its result and into what its
// arguments point to after the call. Only regions that may flow into these
// according to the callee's signature get an edge. A case without
// annotations checks that the spec checks against rustc's borrow checker
// (under `PCG_VALIDITY_CHECKS`) pass on it.

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

// The object type `dyn Sink<'b> + 'd` may hold borrows of `'b`, and of `'d`,
// which the borrow checker relates to `'b` where the call is.
fn put_through_dyn(s: String) -> usize {
    let mut v: Vec<&String> = vec![];
    {
        let d: &mut dyn Sink = &mut v;
        // PCG: bb1[20] post_main: Add Edge call Sink::put at bb1[20]: [_9 before bb1[20]:PostOperands↓'?27 before bb1[20]:PostMain, _8 before bb1[20]:PostOperands↓'?26 before bb1[20]:PostMain, _8 before bb1[20]:PostOperands↓'?25 before bb1[20]:PostMain] -> [_8 before bb1[20]:PostOperands↓'?26 after bb1, _8 before bb1[20]:PostOperands↓'?25 after bb1]
        d.put(&s);
    }
    v.len()
}

// The bound `T: Sink<'c>` lets `put` store `x` into the part `T['c]` of `*t`.
fn put_generic<'c, T: Sink<'c>>(t: &mut T, x: &'c String) {
    // PCG: bb0[4] post_main: Add Edge call Sink::put at bb0[4]: [_4 before bb0[4]:PostOperands↓'?9 before bb0[4]:PostMain, _3 before bb0[4]:PostOperands↓T[RegionVid('?1)] before bb0[4]:PostMain] -> [_3 before bb0[4]:PostOperands↓T[RegionVid('?1)] after bb0]
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
    // PCG: bb0[4] post_main: Add Edge call Sink::put at bb0[4]: [_4 before bb0[4]:PostOperands↓'?13 before bb0[4]:PostMain, _3 before bb0[4]:PostOperands↓<T as Tr<'_>>::Out[RegionVid('?1)] before bb0[4]:PostMain, _3 before bb0[4]:PostOperands↓<T as Tr<'_>>::Out[RegionVid('?12)] before bb0[4]:PostMain] -> [_3 before bb0[4]:PostOperands↓<T as Tr<'_>>::Out[RegionVid('?1)] after bb0, _3 before bb0[4]:PostOperands↓<T as Tr<'_>>::Out[RegionVid('?12)] after bb0]
    // PCG: bb0[4] post_main: Add Edge call Sink::put at bb0[4]: _3 before bb0[4]:PostOperands↓<T as Tr<'_>>::Out[RegionsIn(T)] before bb0[4]:PostMain -> _3 before bb0[4]:PostOperands↓<T as Tr<'_>>::Out[RegionsIn(T)] after bb0
    x.put(s)
}

// The items of `I::IntoIter` are in its part for `'a`, which `I['a]` flows
// into; the rest of `I` flows into its part for `RegionsIn(I)`. So only
// `I['a]` flows into the result, as the signature says.
fn first_item<'a, I: IntoIterator<Item = &'a u32>>(i: I) -> Option<&'a u32> {
    // PCG: bb0[4] post_main: Add Edge call std::iter::IntoIterator::into_iter at bb0[4]: [_4 before bb0[4]:PostOperands↓I[RegionVid('?1)] before bb0[4]:PostMain] -> [_3↓<I as std::iter::IntoIterator>::IntoIter[RegionVid('?1)], _4 before bb0[4]:PostOperands↓I[RegionVid('?1)] after bb0]
    // PCG: bb1[2] post_main: Add Edge call std::iter::Iterator::next at bb1[2]: _2 before bb1[2]:PostOperands↓<I as std::iter::IntoIterator>::IntoIter[RegionsIn(I)] before bb1[2]:PostMain -> _2 before bb1[2]:PostOperands↓<I as std::iter::IntoIterator>::IntoIter[RegionsIn(I)] after bb1
    // PCG: bb1[2] post_main: Add Edge call std::iter::Iterator::next at bb1[2]: [_2 before bb1[2]:PostOperands↓<I as std::iter::IntoIterator>::IntoIter[RegionVid('?1)] before bb1[2]:PostMain] -> [_2 before bb1[2]:PostOperands↓<I as std::iter::IntoIterator>::IntoIter[RegionVid('?1)] after bb1, RETURN↓'?4]
    i.into_iter().next()
}

fn push_into<'b, 'c, C: Extend<&'c u32>>(c: &'b mut C, x: &'c u32) -> &'b mut C {
    c.extend([x]);
    c
}

// `x` may flow into the part `D['c]` of `*d`, and through `D: 'b` on into
// the result's `'b`, if the type `D` stands for holds `'c` data (then `'c:
// 'b`). rustc does not relate `'c` and `'b` here, so the check that each flow
// of a call's spec holds in rustc does not cover flows through a part.
fn push_into_generic<'b, 'c, D: Extend<&'c u32>>(d: &'b mut D, x: &'c u32) -> &'b mut D {
    push_into(d, x)
}

trait Make<'a> {
    type Out;
    fn make(&self) -> Self::Out;
}

// The closure's signature has an erased region in the alias type of its
// parameter, which names no part of the alias's value.
fn alias_in_closure_signature<'a, T: Make<'a>>(t: &T) -> usize {
    let c = |x: <T as Make<'a>>::Out| {
        let _y = x;
        1usize
    };
    c(t.make())
}

// The closure returns its parameter, whose alias type its signature gives
// two distinct regions where its body has one.
fn identity_closure_on_alias<'a, T: Make<'a>>(t: &T) -> <T as Make<'a>>::Out {
    let c = |x: <T as Make<'a>>::Out| x;
    c(t.make())
}

trait HasRef<'a> {
    fn get(&self) -> &'a u32;
}

// The closure returns a reference of `'a`, which only the bound on `T` names:
// the closure's type has no region for it, but its body has.
fn ref_from_bound<'a, T: HasRef<'a>>(ts: &[T]) -> Vec<&'a u32> {
    ts.iter().map(|t| t.get()).collect()
}

struct Ctx<'a, 'b> {
    _r: &'a &'b u32,
}

impl<'a, 'b> Ctx<'a, 'b> {
    // The impl's header implies `'b: 'a`, which the body relies on.
    fn widen_mut(x: &'b mut u32) -> &'a mut u32 {
        x
    }
}

// The result borrows `*v` through the bound that the impl's header implies.
fn call_widen_mut(v: &mut u32) -> u32 {
    // PCG: bb0[5] post_main: Add Edge call Ctx::<'a, 'b>::widen_mut at bb0[5]: _3 before bb0[5]:PostOperands↓'?9 before bb0[5]:PostMain -> r↓'?8
    let r = Ctx::widen_mut(&mut *v);
    *r = 5;
    *v
}

trait Widen<'a, 'b> {
    fn widen(x: &'b mut u32) -> &'a mut u32;
}

impl<'a, 'b> Widen<'a, 'b> for &'a &'b () {
    // The impl's header implies `'b: 'a`.
    fn widen(x: &'b mut u32) -> &'a mut u32 {
        x
    }
}

// The trait's arguments, which the caller proves well-formed, imply `'b: 'a`
// for the impl that the call selects.
fn call_widen_through_trait() -> u32 {
    let mut k = 5u32;
    // PCG: bb0[8] post_main: Add Edge call Widen::widen at bb0[8]: _3 before bb0[8]:PostOperands↓'?9 before bb0[8]:PostMain -> r↓'?8
    let r = <&&() as Widen<'_, '_>>::widen(&mut k);
    *r += 1;
    k
}

// The impl that the body selects for `T` relies on the well-formedness of
// `T`, which the caller proves.
fn widen_generic<'a, 'b, T: Widen<'a, 'b>>(x: &'b mut u32) -> &'a mut u32 {
    T::widen(x)
}

fn call_widen_generic() -> u32 {
    let mut k = 5u32;
    // PCG: bb0[8] post_main: Add Edge call widen_generic at bb0[8]: _3 before bb0[8]:PostOperands↓'?9 before bb0[8]:PostMain -> r↓'?8
    let r = widen_generic::<&&()>(&mut k);
    *r += 1;
    k
}

trait WidenRef<'a, 'b> {
    fn widen_ref(&self, x: &'b mut u32) -> &'a mut u32;
}

impl<'a, 'b> WidenRef<'a, 'b> for &'a &'b () {
    fn widen_ref(&self, x: &'b mut u32) -> &'a mut u32 {
        x
    }
}

fn as_dyn<'x, 'y>(w: &'x &'x &'y ()) -> &'x dyn WidenRef<'x, 'y> {
    w
}

// The impl behind the `dyn` relies on `'y: 'x`, which held where the object
// was made and so holds where it is called.
fn call_widen_dyn() -> u32 {
    let mut k = 5u32;
    let u = ();
    let w = &&u;
    let d = as_dyn(&w);
    // PCG: bb1[10] post_main: Add Edge call WidenRef::widen_ref at bb1[10]: [_10 before bb1[10]:PostOperands↓'?32 before bb1[10]:PostMain, _9 before bb1[10]:PostOperands↓'?29 before bb1[10]:PostMain, _9 before bb1[10]:PostOperands↓'?30 before bb1[10]:PostMain] -> [r↓'?27, _9 before bb1[10]:PostOperands↓'?30 after bb1, _9 before bb1[10]:PostOperands↓'?29 after bb1]
    let r = d.widen_ref(&mut k);
    *r += 1;
    k
}

fn as_opaque<'x, 'y>(w: &'x &'y ()) -> impl WidenRef<'x, 'y> {
    w
}

// The same for the value of an `impl Trait` type.
fn call_widen_opaque() -> u32 {
    let mut k = 5u32;
    let u = ();
    let w = &&u;
    let t = as_opaque(w);
    // PCG: bb1[9] post_main: Add Edge call WidenRef::widen_ref at bb1[9]: [_8 before bb1[9]:PostOperands↓impl WidenRef<'_, '_>[RegionVid('?23)] before bb1[9]:PostMain, _8 before bb1[9]:PostOperands↓impl WidenRef<'_, '_>[RegionVid('?24)] before bb1[9]:PostMain, _9 before bb1[9]:PostOperands↓'?25 before bb1[9]:PostMain] -> [_8 before bb1[9]:PostOperands↓impl WidenRef<'_, '_>[RegionVid('?24)] after bb1, _8 before bb1[9]:PostOperands↓impl WidenRef<'_, '_>[RegionVid('?23)] after bb1, r↓'?21]
    let r = t.widen_ref(&mut k);
    *r += 1;
    drop(t);
    k
}

fn as_fn_ptr<'x, 'y: 'x>() -> fn(&'y mut u32) -> &'x mut u32 {
    |x| x
}

// The same for the function behind a function pointer.
fn call_widen_fn_ptr() -> u32 {
    let mut k = 5u32;
    let p = as_fn_ptr();
    // PCG: bb1[8] post_main: Add Edge call at bb1[8]: _5 before bb1[8]:PostOperands↓'?11 before bb1[8]:PostMain -> r↓'?8
    let r = p(&mut k);
    *r += 1;
    k
}

// `'x` is early-bound, so the type of the function item names it.
fn take_byte<'x>(_: &'x u8)
where
    'x: 'x,
{
}

fn pass<T, F: Fn(T)>(t: T, _f: F) -> T {
    t
}

// A function item holds no borrows: the region that its type names, of its
// parameter, flows nowhere.
fn pass_fn_item(r: &u8) -> &u8 {
    pass(r, take_byte)
}

fn add_static<T>(_c: &'static str, t: T) -> T {
    t
}

// The closure needs the region of the captured reference's target to outlive
// `'static`.
fn map_with_static<T>(s: &&'static str, x: Option<T>) -> Option<T> {
    x.map(|e| add_static(*s, e))
}

trait Unit {
    type Assoc;
}

impl<T> Unit for T {
    type Assoc = ();
}

// The type of `_x` implies `'b: 'a` before it is normalized to `()`.
fn widen_through_alias<'a, 'b>(_x: <&'a &'b () as Unit>::Assoc, y: &'b u32) -> &'a u32 {
    y
}

fn main() {}
