struct T;
struct S<'a>{f: &'a mut Option<T>, g: &'a mut Option<T>}

fn f<'a>(x: &'a mut S<'a>, y: &'a mut S<'a>){
   std::mem::swap(x.f,y.f)
}

fn client<'a>(x: &'a mut S<'a>, y: &'a mut S<'a>){
    // Activation of two-phase borrow:
    f(x,y);
}

fn main(){
}
