// Run loom tests with something like
// ```
// RUSTFLAGS="--cfg loom" cargo test --release loom --features loom
// ```

#[cfg(loom)]
mod loom {
    #[cfg(debug_assertions)]
    compile_error!(
        "Loom tests are typically slow in debug mode. Run them with `--release`"
    );

    use ecow::eco_vec;

    #[test]
    fn smoke() {
        loom::model(|| {
            let mut one = eco_vec![1, 2, 3];
            let two = one.clone();

            loom::thread::spawn(move || {
                let mut three = two.clone();
                three.push(4);

                assert!(three.len() > two.len());
            });

            one.push(4);
            assert_eq!(one, [1, 2, 3, 4]);
        });
    }
}
