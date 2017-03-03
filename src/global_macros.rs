// ref: https://github.com/rust-lang/cargo/pull/1444
macro_rules! is_debug_mode {
    () => {
        cfg!(debug_assertions)
    }
}
