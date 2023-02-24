#[cfg(loom)]
/// Run loom tests with something like
/// ```
/// $ RUSTFLAGS="--cfg loom" cargo test --release loom
/// ```
mod loom;
