use {
    crate::{Guard, Lock, execution_unit::execution_unit_id},
    parking_lot::lock_api::RawMutex,
    std::{
        mem,
        sync::{Barrier, atomic::Ordering::Relaxed},
        thread,
        time::{Duration, Instant},
    },
};

fn assert_default(lock: &Lock) {
    assert_eq!(lock.shared.execution_unit_id.load(Relaxed), 0);
    assert_eq!(lock.shared.tickets.get(), 0);
    assert_eq!(lock.shared.raw_mutex.is_locked(), false);
}

fn run_in_thread<T: Send>(f: impl FnOnce() -> T + Send) -> T {
    thread::scope(|s| s.spawn(|| f()).join().unwrap())
}

#[test]
fn default() {
    let lock = Lock::default();
    assert_default(&lock);
}

#[test]
fn force_unlock() {
    let lock = Lock::default();
    let guard = lock.lock();
    mem::forget(guard);
    assert_eq!(lock.is_locked(), true);
    unsafe {
        lock.force_unlock();
    }
    assert_eq!(lock.is_locked(), false);
    assert_default(&lock);
}

#[test]
fn force_unlock_fair() {
    let lock = Lock::default();
    let guard = lock.lock();
    mem::forget(guard);
    assert_eq!(lock.is_locked(), true);
    unsafe {
        lock.force_unlock_fair();
    }
    assert_eq!(lock.is_locked(), false);
    assert_default(&lock);
}

#[test]
fn is_locked() {
    let lock = Lock::default();
    let guard = lock.lock();
    assert_eq!(lock.is_locked(), true);
    drop(guard);
    assert_eq!(lock.is_locked(), false);
}

#[test]
fn is_locked_by() {
    let lock1 = Lock::default();
    let lock2 = Lock::default();
    let guard1 = &lock1.lock();
    assert_eq!(lock1.is_locked_by(guard1), true);
    assert_eq!(lock2.is_locked_by(guard1), false);
    let guard2 = &lock2.lock();
    assert_eq!(lock1.is_locked_by(guard2), false);
    assert_eq!(lock2.is_locked_by(guard2), true);
    let guard3 = &lock1.lock();
    assert_eq!(lock1.is_locked_by(guard3), true);
    assert_eq!(lock2.is_locked_by(guard3), false);
    assert_eq!(lock1.is_locked_by(guard1), true);
    assert_eq!(lock2.is_locked_by(guard1), false);
}

#[test]
fn is_locked_by_current_thread() {
    let lock = Lock::default();
    assert_eq!(lock.is_locked_by_current_thread(), false);
    run_in_thread(|| {
        assert_eq!(lock.is_locked_by_current_thread(), false);
    });
    {
        let _guard = lock.lock();
        assert_eq!(lock.is_locked_by_current_thread(), true);
        run_in_thread(|| {
            assert_eq!(lock.is_locked_by_current_thread(), false);
        });
    }
    assert_eq!(lock.is_locked_by_current_thread(), false);
    run_in_thread(|| {
        assert_eq!(lock.is_locked_by_current_thread(), false);
    });
    let barrier1 = Barrier::new(2);
    let barrier2 = Barrier::new(2);
    thread::scope(|s| {
        let handle = s.spawn(|| {
            let _guard = lock.lock();
            assert_eq!(lock.is_locked_by_current_thread(), true);
            barrier1.wait();
            barrier2.wait();
        });
        barrier1.wait();
        assert_eq!(lock.is_locked(), true);
        assert_eq!(lock.is_locked_by_current_thread(), false);
        barrier2.wait();
        handle.join().unwrap();
    });
}

#[test]
fn lock() {
    let lock = Lock::default();
    run_in_thread(|| {
        assert!(lock.try_lock().is_some());
    });
    let guard1 = lock.lock();
    assert_eq!(
        lock.shared.execution_unit_id.load(Relaxed),
        execution_unit_id()
    );
    assert_eq!(lock.shared.tickets.get(), 1);
    run_in_thread(|| {
        assert!(lock.try_lock().is_none());
    });
    let guard2 = lock.lock();
    assert_eq!(
        lock.shared.execution_unit_id.load(Relaxed),
        execution_unit_id()
    );
    assert_eq!(lock.shared.tickets.get(), 2);
    run_in_thread(|| {
        assert!(lock.try_lock().is_none());
    });
    drop(guard2);
    assert_eq!(
        lock.shared.execution_unit_id.load(Relaxed),
        execution_unit_id()
    );
    assert_eq!(lock.shared.tickets.get(), 1);
    run_in_thread(|| {
        assert!(lock.try_lock().is_none());
    });
    drop(guard1);
    assert_eq!(lock.shared.execution_unit_id.load(Relaxed), 0);
    assert_eq!(lock.shared.tickets.get(), 0);
    run_in_thread(|| {
        assert!(lock.try_lock().is_some());
    });
}

#[test]
fn make_guard_unchecked() {
    let lock = Lock::default();
    let guard = lock.lock();
    mem::forget(guard);
    assert_eq!(
        lock.shared.execution_unit_id.load(Relaxed),
        execution_unit_id(),
    );
    assert_eq!(lock.shared.tickets.get(), 1);
    let guard = unsafe { lock.make_guard_unchecked() };
    assert_eq!(
        lock.shared.execution_unit_id.load(Relaxed),
        execution_unit_id(),
    );
    assert_eq!(lock.shared.tickets.get(), 1);
    drop(guard);
    assert_default(&lock);
}

#[test]
fn try_lock() {
    let lock = Lock::default();
    assert!(lock.try_lock().is_some());
    run_in_thread(|| {
        assert!(lock.try_lock().is_some());
    });
    let guard = lock.lock();
    assert!(lock.try_lock().is_some());
    run_in_thread(|| {
        assert!(lock.try_lock().is_none());
    });
    drop(guard);
    assert!(lock.try_lock().is_some());
    run_in_thread(|| {
        assert!(lock.try_lock().is_some());
    });
}

#[test]
fn try_lock_for() {
    let lock = Lock::default();
    let duration = Duration::from_millis(100);
    assert!(lock.try_lock_for(duration).is_some());
    run_in_thread(|| {
        assert!(lock.try_lock_for(duration).is_some());
    });
    let guard = lock.lock();
    assert!(lock.try_lock_for(duration).is_some());
    run_in_thread(|| {
        let start = Instant::now();
        assert!(lock.try_lock_for(duration).is_none());
        let elapsed = start.elapsed();
        assert!(elapsed >= duration);
    });
    drop(guard);
    assert!(lock.try_lock_for(duration).is_some());
    run_in_thread(|| {
        assert!(lock.try_lock_for(duration).is_some());
    });
}

#[test]
fn try_lock_until() {
    let lock = Lock::default();
    let duration = Duration::from_millis(100);
    assert!(lock.try_lock_until(Instant::now() + duration).is_some());
    run_in_thread(|| {
        assert!(lock.try_lock_until(Instant::now() + duration).is_some());
    });
    let guard = lock.lock();
    assert!(lock.try_lock_until(Instant::now() + duration).is_some());
    run_in_thread(|| {
        let start = Instant::now();
        assert!(lock.try_lock_until(start + duration).is_none());
        let elapsed = start.elapsed();
        assert!(elapsed >= duration);
    });
    drop(guard);
    assert!(lock.try_lock_until(Instant::now() + duration).is_some());
    run_in_thread(|| {
        assert!(lock.try_lock_until(Instant::now() + duration).is_some());
    });
}

fn unlock_test(mut unlocker: impl FnMut(Guard<'_>)) {
    let lock = Lock::default();
    run_in_thread(|| {
        assert!(lock.try_lock().is_some());
    });
    let guard = lock.lock();
    run_in_thread(|| {
        assert!(lock.try_lock().is_none());
    });
    unlocker(guard);
    assert_default(&lock);
    run_in_thread(|| {
        assert!(lock.try_lock().is_some());
    });
    let guard1 = lock.lock();
    run_in_thread(|| {
        assert!(lock.try_lock().is_none());
    });
    let guard2 = lock.lock();
    run_in_thread(|| {
        assert!(lock.try_lock().is_none());
    });
    unlocker(guard1);
    run_in_thread(|| {
        assert!(lock.try_lock().is_none());
    });
    unlocker(guard2);
    run_in_thread(|| {
        assert!(lock.try_lock().is_some());
    });
}

#[test]
fn drop_guard() {
    unlock_test(|guard| drop(guard));
}

#[test]
fn unlock_fair() {
    unlock_test(|guard| guard.unlock_fair());
}

trait Unlocked {
    fn unlocked<T>(guard: &mut Guard<'_>, f: impl FnOnce() -> T) -> T;
}

struct UnfairUnlocked;

impl Unlocked for UnfairUnlocked {
    fn unlocked<T>(guard: &mut Guard<'_>, f: impl FnOnce() -> T) -> T {
        guard.unlocked(f)
    }
}

struct FairUnlocked;

impl Unlocked for FairUnlocked {
    fn unlocked<T>(guard: &mut Guard<'_>, f: impl FnOnce() -> T) -> T {
        guard.unlocked_fair(f)
    }
}

fn unlocked_test<T: Unlocked>() {
    let lock = Lock::default();
    let assert_good = || {
        run_in_thread(|| {
            assert!(lock.try_lock().is_some());
        });
    };
    let assert_bad = || {
        run_in_thread(|| {
            assert!(lock.try_lock().is_none());
        });
    };
    assert_good();
    let mut guard = lock.lock();
    assert_bad();
    T::unlocked(&mut guard, || {
        assert_good();
    });
    assert_bad();
    drop(guard);
    assert_good();
    let mut guard1 = lock.lock();
    let mut guard2 = lock.lock();
    assert_bad();
    T::unlocked(&mut guard1, || {
        assert_bad();
    });
    T::unlocked(&mut guard1, || {
        assert_bad();
        T::unlocked(&mut guard2, || {
            assert_good();
        });
        assert_bad();
    });
    drop(guard1);
    drop(guard2);
    assert_good();
}

#[test]
fn unlocked() {
    unlocked_test::<UnfairUnlocked>();
}

#[test]
fn unlocked_fair() {
    unlocked_test::<FairUnlocked>();
}

#[test]
fn eq() {
    let lock1 = Lock::default();
    let lock2 = Lock::default();
    assert_eq!(lock1, lock1);
    assert_ne!(lock1, lock2);
    assert_ne!(lock1, lock2);
    assert_eq!(lock2, lock2);
}
