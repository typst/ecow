mod vec;

#[cfg(debug_assertions)]
compile_error!("Loom tests are typically slow in debug mode. Run them with `--release`");
