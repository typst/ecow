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
