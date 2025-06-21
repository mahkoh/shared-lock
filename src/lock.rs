#[cfg(doc)]
use crate::locked::Locked;
use {
    crate::execution_unit::execution_unit_id,
    opera::{PhantomNotSend, PhantomNotSync},
    parking_lot::{
        RawMutex,
        lock_api::{RawMutex as RawMutexTrait, RawMutexFair, RawMutexTimed},
    },
    run_on_drop::on_drop,
    static_assertions::assert_not_impl_any,
    std::{
        cell::Cell,
        fmt::{Debug, Formatter},
        mem::{self, ManuallyDrop},
        ptr,
        sync::{
            Arc,
            atomic::{AtomicUsize, Ordering::Relaxed},
        },
        time::{Duration, Instant},
    },
};

#[cfg(test)]
mod tests;

/// A re-entrant lock that can be used to protect multiple objects.
///
/// Locking this lock automatically gives access to all objects protected by it.
///
/// # Example
///
/// ```
/// use shared_lock::Lock;
///
/// let lock = Lock::default();
/// let locked1 = lock.wrap(1);
/// let locked2 = lock.wrap(2);
/// let guard = &lock.lock();
/// assert_eq!(*locked1.get(guard), 1);
/// assert_eq!(*locked2.get(guard), 2);
/// ```
#[derive(Clone, Default)]
pub struct Lock {
    shared: Arc<Shared>,
}

struct Shared {
    // We enforce the following invariants:
    // 1. if tickets > 0, then raw_mutex is locked
    // 2. if execution_unit_id != 0, then the mutex is locked and the execution unit with
    //    the id execution_unit_id locked it
    // We say that the current execution unit owns a ticket if tickets > 0 and
    // execution_unit_id is the execution_unit_id of the current execution unit.
    raw_mutex: RawMutex,
    // Mutations of this field are protected by the raw_mutex.
    execution_unit_id: AtomicUsize,
    // This field is protected by the raw_mutex.
    tickets: Cell<u64>,
}

/// An acquired lock guard.
///
/// This object is created by calling [`Lock::lock`] or one of the other locking
/// functions.
///
/// A [`Guard`] can be used to access [`Locked`] data by calling [`Locked::get`].
///
/// Each [`Guard`] represents a ticket of the [`Lock`] it was created from. A thread can
/// have any number of tickets and while a thread holds at least 1 ticket of a [`Lock`],
/// no other thread can acquire a ticket from that [`Lock`].
///
/// A [`Guard`] can temporarily give up its ticket by calling [`Guard::unlocked`] or
/// [`Guard::unlocked_fair`]. The ticket will be restored before those functions return.
/// The [`Guard`] is inaccessible while the function is running.
///
/// Dropping the [`Guard`] or calling [`Guard::unlock_fair`] consumes the ticket.
///
/// The [`Guard`] can be passed to [`mem::forget`] to leak the ticket without leaking any
/// memory.
///
/// # Example
///
/// ```
/// use shared_lock::Lock;
///
/// let lock = Lock::default();
/// let _guard = lock.lock();
/// ```
pub struct Guard<'a> {
    lock: &'a Lock,
    _phantom_not_send: PhantomNotSend,
    _phantom_not_sync: PhantomNotSync,
}

unsafe impl Send for Lock {}

unsafe impl Sync for Lock {}

assert_not_impl_any!(Guard<'_>: Sync, Send);

impl Default for Shared {
    fn default() -> Self {
        Self {
            raw_mutex: RawMutex::INIT,
            execution_unit_id: AtomicUsize::new(0),
            tickets: Cell::new(0),
        }
    }
}

macro_rules! maybe_lock_fast {
    ($slf:expr, $guard:ident, $ret:expr) => {
        let shared = &*$slf.shared;
        if shared.execution_unit_id.load(Relaxed) == execution_unit_id() {
            // SAFETY: - We have just checked that execution_unit_id contains the ID of
            //           the current execution unit.
            //         - By the invariants, this means that the current execution unit is
            //           holding the mutex.
            //         - Therefore no other execution unit is allowed to modify the
            //           field.
            let $guard = unsafe { $slf.add_ticket() };
            return $ret;
        }
    };
}

impl Lock {
    /// Forcibly consumes a ticket.
    ///
    /// This can be used to consume the ticket of a [`Guard`] that was passed to
    /// [`mem::forget`].
    ///
    /// # Safety
    ///
    /// - The current thread must own a ticket.
    /// - The invariant that each [`Guard`] owns a ticket must be upheld whenever a
    ///   [`Guard`] is used or dropped.
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem;
    /// use shared_lock::Lock;
    ///
    /// let lock = Lock::default();
    /// let guard = lock.lock();
    /// assert!(lock.is_locked());
    /// mem::forget(guard);
    /// // SAFETY: This consumes the ticket from the guard.
    /// unsafe {
    ///     lock.force_unlock();
    /// }
    /// assert!(!lock.is_locked());
    /// ```
    #[inline]
    pub unsafe fn force_unlock(&self) {
        // SAFETY: - The calling thread owning a ticket means that execution_unit_id is
        //           the ID of the current execution unit and tickets > 0.
        unsafe {
            self.force_unlock_::<false>();
        }
    }

    /// Forcibly consumes a ticket.
    ///
    /// If this causes the number tickets to go to 0, the underlying mutex will be
    /// unlocked fairly.
    ///
    /// This can be used to consume the ticket of a [`Guard`] that was passed to
    /// [`mem::forget`].
    ///
    /// # Safety
    ///
    /// - The current thread must own a ticket.
    /// - The invariant that each [`Guard`] owns a ticket must be upheld whenever a
    ///   [`Guard`] is used or dropped.
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem;
    /// use shared_lock::Lock;
    ///
    /// let lock = Lock::default();
    /// let guard = lock.lock();
    /// assert!(lock.is_locked());
    /// mem::forget(guard);
    /// // SAFETY: This consumes the ticket from the guard.
    /// unsafe {
    ///     lock.force_unlock_fair();
    /// }
    /// assert!(!lock.is_locked());
    /// ```
    #[inline]
    pub unsafe fn force_unlock_fair(&self) {
        // SAFETY: - The calling thread owning a ticket means that execution_unit_id is
        //           the ID of the current execution unit and tickets > 0.
        unsafe {
            self.force_unlock_::<true>();
        }
    }

    /// # Safety
    ///
    /// - execution_unit_id must be the ID of the calling execution unit.
    /// - tickets must be > 0.
    #[inline]
    unsafe fn force_unlock_<const FAIR: bool>(&self) {
        let shared = &*self.shared;
        // SAFETY: - By the safety requirements of this function, execution_unit_id is the
        //           ID of the current execution unit.
        //         - By the invariants, the current execution unit is holding the lock.
        //         - Therefore we are allowed to access this field.
        let guards = shared.tickets.get();
        debug_assert!(guards > 0);
        // SAFETY: - Dito.
        shared.tickets.set(guards - 1);
        if guards == 1 {
            // SAFETY: - We've just set tickets to 0.
            //         - The execution_unit_id requirements is forwarded to the caller of
            //           this function.
            unsafe {
                self.force_unlock_slow::<FAIR>();
            }
        }
    }

    /// # Safety
    ///
    /// - tickets must be 0
    /// - execution_unit_id must be the execution unit ID of the current execution unit
    #[cold]
    #[inline]
    unsafe fn force_unlock_slow<const FAIR: bool>(&self) {
        debug_assert_eq!(
            self.shared.execution_unit_id.load(Relaxed),
            execution_unit_id(),
        );
        // SAFETY: - By the safety requirements of this function, execution_unit_id is
        //           the execution unit of the calling execution unit.
        //         - By the invariants, the current execution unit is holding the mutex.
        //         - Therefore we are allowed to access this field.
        debug_assert_eq!(self.shared.tickets.get(), 0);
        self.shared.execution_unit_id.store(0, Relaxed);
        // SAFETY: - By the safety requirements of this function, the number of tickets is
        //           0.
        //         - As discussed above, the current execution unit is holding the mutex.
        unsafe {
            if FAIR {
                self.shared.raw_mutex.unlock_fair();
            } else {
                self.shared.raw_mutex.unlock();
            }
        }
    }

    /// Returns whether this lock is locked.
    ///
    /// # Example
    ///
    /// ```
    /// use shared_lock::Lock;
    ///
    /// let lock = Lock::default();
    /// assert!(!lock.is_locked());
    /// let _guard = lock.lock();
    /// assert!(lock.is_locked());
    /// ```
    #[inline]
    pub fn is_locked(&self) -> bool {
        self.shared.raw_mutex.is_locked()
    }

    /// Returns whether this lock is locked by the guard.
    ///
    /// # Example
    ///
    /// ```
    /// use shared_lock::Lock;
    ///
    /// let lock1 = Lock::default();
    /// let lock2 = Lock::default();
    ///
    /// let guard1 = &lock1.lock();
    /// let guard2 = &lock2.lock();
    ///
    /// assert!(lock1.is_locked_by(&guard1));
    /// assert!(!lock1.is_locked_by(&guard2));
    /// ```
    #[inline]
    pub fn is_locked_by(&self, guard: &Guard<'_>) -> bool {
        self == guard.lock
    }

    /// Returns whether the current thread is holding the lock.
    ///
    /// # Example
    ///
    /// ```
    /// use std::thread;
    /// use shared_lock::Lock;
    ///
    /// let lock = Lock::default();
    /// let _guard = lock.lock();
    /// assert!(lock.is_locked_by_current_thread());
    ///
    /// thread::scope(|scope| {
    ///     let handle = scope.spawn(|| {
    ///         assert!(!lock.is_locked_by_current_thread());
    ///     });
    ///     handle.join().unwrap();
    /// });
    /// ```
    #[inline]
    pub fn is_locked_by_current_thread(&self) -> bool {
        let shared = &*self.shared;
        shared.execution_unit_id.load(Relaxed) == execution_unit_id()
    }

    /// Acquires this lock.
    ///
    /// If the lock is held by another thread, then this function will block until it is
    /// able to acquire the lock. If the current thread has already acquired the lock, the
    /// function returns immediately.
    ///
    /// # Example
    ///
    /// ```
    /// use shared_lock::Lock;
    ///
    /// let lock = Lock::default();
    /// let _guard = lock.lock();
    /// ```
    #[inline]
    pub fn lock(&self) -> Guard<'_> {
        maybe_lock_fast!(self, guard, guard);
        self.lock_slow()
    }

    #[cold]
    #[inline(always)]
    fn lock_slow(&self) -> Guard<'_> {
        self.shared.raw_mutex.lock();
        // SAFETY: - We've just locked the mutex.
        unsafe { self.add_ticket_after_lock() }
    }

    /// # Safety
    ///
    /// - The current execution unit must just have succeeded in locking the mutex.
    #[inline]
    unsafe fn add_ticket_after_lock(&self) -> Guard<'_> {
        let shared = &*self.shared;
        // SAFETY: - By the requirements of this function, we've just locked the mutex.
        //         - Therefore
        //           - we are allowed to mutate this field.
        //           - setting the execution_unit_id to the ID of the current execution
        //             unit upholds the invariant.
        shared.execution_unit_id.store(execution_unit_id(), Relaxed);
        // SAFETY: - We have just set execution_unit_id to the ID of the current execution
        //           unit.
        //         - Since we're holding the lock, no other thread is allowed to modify
        //           the field.
        unsafe { self.add_ticket() }
    }

    /// # Safety
    ///
    /// - execution_unit_id must be the ID of the current execution unit.
    #[inline]
    unsafe fn add_ticket(&self) -> Guard<'_> {
        let shared = &*self.shared;
        // SAFETY: - By the requirements of this function, execution_unit_id is the ID of
        //           the current execution unit.
        //         - By the invariants, this means that the current execution unit it
        //           holding the mutex.
        let guards = shared.tickets.get();
        if guards == u64::MAX {
            #[cold]
            fn never() -> ! {
                #[allow(clippy::empty_loop)]
                loop {}
            }
            never();
        }
        // SAFETY: - Dito regarding the ability to access tickets.
        //         - Since the current execution unit is holding the mutex, setting
        //           tickets to guards + 1 > 0 upholds the invariant.
        shared.tickets.set(guards + 1);
        // SAFETY: - We've just added a ticket and we're assigning ownership of that
        //           ticket to the new Guard.
        //         - Therefore the requirements that the invariant is upheld is unaffected
        //           by this call.
        unsafe { self.make_guard_unchecked_() }
    }

    /// Creates a new [`Guard`] without checking if the lock is held.
    ///
    /// # Safety
    ///
    /// - The invariant that each [`Guard`] owns a ticket must be upheld whenever a
    ///   [`Guard`] is used or dropped.
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem;
    /// use shared_lock::Lock;
    ///
    /// let lock = Lock::default();
    /// mem::forget(lock.lock());
    /// // SAFETY: This recovers the guard we just forgot.
    /// let _guard = unsafe {
    ///     lock.make_guard_unchecked()
    /// };
    /// ```
    #[inline]
    pub unsafe fn make_guard_unchecked(&self) -> Guard<'_> {
        // SAFETY: The requirement is forwarded to the caller.
        unsafe { self.make_guard_unchecked_() }
    }

    /// # Safety
    ///
    /// - The invariant that each [`Guard`] owns a ticket must be upheld whenever a
    ///   [`Guard`] is used or dropped.
    #[inline]
    unsafe fn make_guard_unchecked_(&self) -> Guard<'_> {
        Guard {
            lock: self,
            _phantom_not_send: Default::default(),
            _phantom_not_sync: Default::default(),
        }
    }

    /// Attempts to acquire this lock.
    ///
    /// If the lock cannot be acquired at this time, `None` is returned. Otherwise a guard
    /// is returned and the lock will be unlocked when the guard is dropped.
    ///
    /// This function does not block.
    ///
    /// # Example
    ///
    /// ```
    /// use std::thread;
    /// use std::time::{Duration, Instant};
    /// use shared_lock::Lock;
    ///
    /// let timeout = Duration::from_millis(200);
    /// let lock = Lock::default();
    /// let _guard = lock.lock();
    /// // The same thread can lock the lock again.
    /// assert!(lock.try_lock().is_some());
    ///
    /// thread::scope(|scope| {
    ///     let join_handle = scope.spawn(|| {
    ///         // Another thread cannot lock the lock.
    ///         assert!(lock.try_lock().is_none());
    ///     });
    ///     join_handle.join().unwrap();
    /// });
    /// ```
    #[inline]
    pub fn try_lock(&self) -> Option<Guard<'_>> {
        maybe_lock_fast!(self, guard, Some(guard));
        self.try_lock_slow()
    }

    #[cold]
    #[inline]
    fn try_lock_slow(&self) -> Option<Guard<'_>> {
        self.shared.raw_mutex.try_lock().then(|| {
            // SAFETY: - We've just locked the mutex.
            unsafe { self.add_ticket_after_lock() }
        })
    }

    /// Attempts to acquire this lock until a timeout has expired.
    ///
    /// If the lock cannot be acquired before the timeout expires, `None` is returned.
    /// Otherwise a guard is returned and the lock will be unlocked when the guard is
    /// dropped.
    ///
    /// # Example
    ///
    /// ```
    /// use std::thread;
    /// use std::time::{Duration, Instant};
    /// use shared_lock::Lock;
    ///
    /// let timeout = Duration::from_millis(200);
    /// let lock = Lock::default();
    /// let _guard = lock.lock();
    ///
    /// thread::scope(|scope| {
    ///     let join_handle = scope.spawn(|| {
    ///         let guard = lock.try_lock_for(timeout);
    ///         assert!(guard.is_none());
    ///     });
    ///     join_handle.join().unwrap();
    /// });
    /// ```
    #[inline]
    pub fn try_lock_for(&self, duration: Duration) -> Option<Guard<'_>> {
        maybe_lock_fast!(self, guard, Some(guard));
        self.try_lock_for_slow(duration)
    }

    #[cold]
    #[inline]
    fn try_lock_for_slow(&self, duration: Duration) -> Option<Guard<'_>> {
        self.shared.raw_mutex.try_lock_for(duration).then(|| {
            // SAFETY: - We've just locked the mutex.
            unsafe { self.add_ticket_after_lock() }
        })
    }

    /// Attempts to acquire this lock until a timeout is reached.
    ///
    /// If the lock cannot be acquired before the timeout expires, `None` is returned.
    /// Otherwise a guard is returned and the lock will be unlocked when the guard is
    /// dropped.
    ///
    /// # Example
    ///
    /// ```
    /// use std::thread;
    /// use std::time::{Duration, Instant};
    /// use shared_lock::Lock;
    ///
    /// let timeout = Instant::now() + Duration::from_millis(200);
    /// let lock = Lock::default();
    /// let _guard = lock.lock();
    ///
    /// thread::scope(|scope| {
    ///     let join_handle = scope.spawn(|| {
    ///         let guard = lock.try_lock_until(timeout);
    ///         assert!(guard.is_none());
    ///     });
    ///     join_handle.join().unwrap();
    /// });
    /// ```
    #[inline]
    pub fn try_lock_until(&self, instant: Instant) -> Option<Guard<'_>> {
        maybe_lock_fast!(self, guard, Some(guard));
        self.try_lock_until_slow(instant)
    }

    #[cold]
    #[inline]
    fn try_lock_until_slow(&self, instant: Instant) -> Option<Guard<'_>> {
        self.shared.raw_mutex.try_lock_until(instant).then(|| {
            // SAFETY: - We've just locked the mutex.
            unsafe { self.add_ticket_after_lock() }
        })
    }

    #[inline]
    pub(crate) fn addr(&self) -> *const u8 {
        let addr: *const Shared = &*self.shared;
        addr.cast()
    }
}

impl Debug for Lock {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Lock")
            .field("id", &self.addr())
            .finish_non_exhaustive()
    }
}

impl PartialEq for Lock {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        ptr::eq::<Shared>(&*self.shared, &*other.shared)
    }
}

impl Eq for Lock {}

impl Guard<'_> {
    /// Unlocks this guard.
    ///
    /// If this causes the number of tickets to drop to 0, the underlying mutex is
    /// unlocked using a fair protocol.
    ///
    /// # Example
    ///
    /// ```
    /// use shared_lock::Lock;
    ///
    /// let lock = Lock::default();
    /// let guard = lock.lock();
    /// guard.unlock_fair();
    /// ```
    #[inline]
    pub fn unlock_fair(self) {
        let slf = ManuallyDrop::new(self);
        // SAFETY: - By the invariants, this guard owns a ticket which means that
        //           the execution_unit_id is the ID of the current execution unit.
        //         - Since we've wrapped self in ManuallyDrop, we know that it won't be
        //           used after this.
        unsafe {
            slf.lock.force_unlock_fair();
        }
    }

    /// Unlocks this guard, runs a function, and then re-acquires the guard.
    ///
    /// If another guard exists, then other threads will not be able to acquire the lock
    /// even while the function is running.
    ///
    /// # Example
    ///
    /// ```
    /// use shared_lock::Lock;
    ///
    /// let lock = Lock::default();
    /// let locked = lock.wrap(1);
    /// let mut guard = lock.lock();
    /// assert_eq!(*locked.get(&guard), 1);
    /// guard.unlocked(|| {
    ///     assert!(!lock.is_locked());
    /// });
    /// assert_eq!(*locked.get(&guard), 1);
    /// ```
    #[inline]
    pub fn unlocked<T>(&mut self, f: impl FnOnce() -> T) -> T {
        self.unlocked_::<_, false>(f)
    }

    /// Unlocks this guard fairly, runs a function, and then re-acquires the guard.
    ///
    /// If another guard exists, then other threads will not be able to acquire the lock
    /// even while the function is running.
    ///
    /// # Example
    ///
    /// ```
    /// use shared_lock::Lock;
    ///
    /// let lock = Lock::default();
    /// let locked = lock.wrap(1);
    /// let mut guard = lock.lock();
    /// assert_eq!(*locked.get(&guard), 1);
    /// guard.unlocked_fair(|| {
    ///     assert!(!lock.is_locked());
    /// });
    /// assert_eq!(*locked.get(&guard), 1);
    /// ```
    #[inline]
    pub fn unlocked_fair<T>(&mut self, f: impl FnOnce() -> T) -> T {
        self.unlocked_::<_, true>(f)
    }

    #[inline]
    fn unlocked_<T, const FAIR: bool>(&mut self, f: impl FnOnce() -> T) -> T {
        // SAFETY: - Since we have have a mutable reference, this guard cannot current be
        //           used to access any locked data (since that borrows the guard).
        //         - Any two guards of the same lock are interchangeable.
        //         - This unlock operation morally consumes the guard. On drop, we restore
        //           it by acquiring a new guard and then forgetting it.
        unsafe {
            self.lock.force_unlock_::<FAIR>();
        }
        let _lock = on_drop(|| {
            let guard = self.lock.lock();
            mem::forget(guard);
        });
        f()
    }
}

impl Drop for Guard<'_> {
    #[inline]
    fn drop(&mut self) {
        // SAFETY: - By the invariants, this guard owns a ticket which means that
        //           the execution_unit_id is the ID of the current execution unit.
        unsafe {
            self.lock.force_unlock_::<false>();
        }
    }
}

impl Debug for Guard<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Guard")
            .field("lock_id", &self.lock.addr())
            .finish_non_exhaustive()
    }
}
