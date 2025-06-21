use {crate::execution_unit::execution_unit_id, std::thread};

#[test]
fn eu() {
    assert_ne!(execution_unit_id(), 0);
    assert_eq!(execution_unit_id(), execution_unit_id());
    let other = thread::spawn(|| execution_unit_id()).join().unwrap();
    assert_ne!(execution_unit_id(), other);
}
