// option PCG_ALLOW_BORROWCK_ERRORS: true

fn assign_twice() -> u32 {
    let x = 0;
    x = 1;
    x
}

fn require_send<T: Send>(_: T) {}

async fn yield_now() {}

// E0277, from a coroutine obligation that type checking defers to the start
// of rustc's `mir_borrowck`.
fn future_not_send() {
    require_send(async {
        let r = std::rc::Rc::new(0);
        yield_now().await;
        drop(r);
    });
}
