struct List<'a, T> {
    head: &'a mut T,
    tail: Option<Box<List<'a, T>>>,
}

impl<'a, T> List<'a, T> {
    fn push(&mut self, value: &'a mut T) {}
}

fn main() {
    let mut v1 = 1;
    let mut v2 = 2;
    let mut v3 = 3;
    let mut rv1 = &mut v1;
    let mut rv2 = &mut v2;
    let mut rv3 = &mut v3;
    let mut list: List<'_, i32> = List {
        head: rv1,
        tail: None,
    };
    list.push(rv2);
    // list|'a should not be a placeholder here
// PCG: bb2[0] post_main: call List::<'a, T>::push at bb1[9]: [_11 before bb1[9]:PostOperands↓'?21 before bb1[9]:PostMain, _12 before bb1[9]:PostOperands↓'?22 before bb1[9]:PostMain] -> [_11 before bb1[9]:PostOperands↓'?21 after bb1]
// PCG: bb2[0] post_main: list↓'?17 before bb1[6]:PostMain -> _11 before bb1[9]:PostOperands↓'?21 before bb1[9]:PostMain
// PCG: bb2[0] post_main: list↓'?17 before bb1[6]:PostMain -> list↓'?17
    let y = 1;
    list.push(rv3);
}
