use {
    crate::Lock,
    std::{
        cell::{Cell, RefCell},
        thread,
    },
};

#[test]
fn deref() {
    let lock = Lock::default();
    let locked = lock.wrap(1);
    assert_eq!(&lock, &*locked);
}

#[test]
fn wrap() {
    let lock = Lock::default();
    let locked = lock.wrap(1);
    let guard = &lock.lock();
    assert_eq!(*locked.get(guard), 1);
    assert_eq!(locked.into_inner(), 1);
}

#[test]
#[should_panic(expected = "guard does not guard this object")]
fn get_wrong_lock() {
    let lock1 = Lock::default();
    let lock2 = Lock::default();
    let locked = lock1.wrap(1);
    let guard = &lock2.lock();
    locked.get(guard);
}

#[test]
fn get() {
    let lock = Lock::default();
    let locked = lock.wrap(Cell::new(1));
    let guard = &lock.lock();
    let v1 = locked.get(guard);
    let v2 = locked.get(guard);
    let v3 = locked.get(guard);
    assert_eq!(v1.get(), 1);
    assert_eq!(v2.get(), 1);
    v1.set(2);
    assert_eq!(v2.get(), 2);
    assert_eq!(v3.get(), 2);
    let v4 = locked.get(guard);
    assert_eq!(v4.get(), 2);
}

#[test]
fn get2() {
    let lock = Lock::default();
    let locked = lock.wrap(RefCell::new(Box::new(1)));
    let guard = &lock.lock();
    let v1 = locked.get(guard);
    let v2 = locked.get(guard);
    let v3 = locked.get(guard);
    assert_eq!(**v1.borrow(), 1);
    assert_eq!(**v2.borrow(), 1);
    **v1.borrow_mut() = 2;
    assert_eq!(**v2.borrow(), 2);
    assert_eq!(**v3.borrow(), 2);
    let v4 = locked.get(guard);
    assert_eq!(**v4.borrow(), 2);
}

#[test]
fn into_inner() {
    let lock = Lock::default();
    let locked = lock.wrap(RefCell::new(Box::new(1)));
    let guard = &lock.lock();
    let v1 = locked.get(guard);
    assert_eq!(**v1.borrow(), 1);
    **v1.borrow_mut() = 2;
    assert_eq!(*locked.into_inner().into_inner(), 2);
}

#[test]
fn get_mut() {
    let lock = Lock::default();
    let mut locked = lock.wrap(RefCell::new(Box::new(1)));
    locked.get_mut().replace(Box::new(2));
    let guard = &lock.lock();
    let v1 = locked.get(guard);
    assert_eq!(**v1.borrow(), 2);
    *v1.borrow_mut() = Box::new(3);
    assert_eq!(*locked.into_inner().into_inner(), 3);
}

#[test]
fn get_ptr() {
    let lock = Lock::default();
    let locked = lock.wrap(1);
    let ptr1 = locked.data_ptr();
    let guard = &lock.lock();
    let ptr2: *const i32 = locked.get(guard);
    assert_eq!(ptr1, ptr2);
}

#[test]
fn debug() {
    let s = "hello world";
    let lock = Lock::default();
    let locked = lock.wrap(s);
    assert!(format!("{locked:?}").contains(s));
    let _guard = &lock.lock();
    assert!(format!("{locked:?}").contains(s));
    let formatted = thread::scope(|scope| scope.spawn(|| format!("{locked:?}")).join().unwrap());
    assert!(!formatted.contains(s));
    assert!(formatted.contains("<locked>"));
}
