#[cfg(doc)]
use std::sync::Arc;
use {
    crate::{Lock, lock::Guard},
    debug_fn::debug_fn,
    opera::PhantomNotSync,
    static_assertions::{assert_impl_all, assert_not_impl_any},
    std::{
        cell::UnsafeCell,
        fmt::{Debug, Formatter},
        ops::Deref,
    },
};

#[cfg(test)]
mod tests;

/// A value locked by a [`Lock`].
///
/// Objects of this type can be created with [`Lock::wrap`].
///
/// This object is essentially the same as the wrapped value with the following
/// differences:
///
/// - `Locked<T>: Sync` if and only if `T: Send`.
/// - Only one thread can access the contained value at a time.
///
/// This object derefs to the underlying [`Lock`].
///
/// # Example
///
/// ```
/// use std::cell::Cell;
/// use std::sync::Arc;
/// use static_assertions::assert_impl_all;
/// use shared_lock::{Lock, Locked};
///
/// struct Context {
///     lock: Lock,
///     global_value: Locked<Cell<u64>>,
/// }
///
/// struct Child {
///     context: Arc<Context>,
///     local_value: Locked<Cell<u64>>,
/// }
///
/// impl Child {
///     fn increment(&self) {
///         let guard = &self.context.lock.lock();
///         let local_value = self.local_value.get(guard);
///         local_value.set(local_value.get() + 1);
///         let global_value = self.context.global_value.get(guard);
///         global_value.set(global_value.get() + 1);
///     }
/// }
///
/// assert_impl_all!(Context: Send, Sync);
/// assert_impl_all!(Child: Send, Sync);
///
/// let lock = Lock::default();
/// let context = Arc::new(Context {
///     global_value: lock.wrap(Cell::new(0)),
///     lock,
/// });
/// let child1 = Arc::new(Child {
///     context: context.clone(),
///     local_value: context.lock.wrap(Cell::new(0)),
/// });
/// let child2 = Arc::new(Child {
///     context: context.clone(),
///     local_value: context.lock.wrap(Cell::new(0)),
/// });
///
/// child1.increment();
/// child2.increment();
/// child2.increment();
///
/// let guard = &context.lock.lock();
/// assert_eq!(child1.local_value.get(guard).get(), 1);
/// assert_eq!(child2.local_value.get(guard).get(), 2);
/// assert_eq!(context.global_value.get(guard).get(), 3);
/// ```
pub struct Locked<T>
where
    T: ?Sized,
{
    lock: Lock,
    _phantom_not_sync: PhantomNotSync,
    value: UnsafeCell<T>,
}

#[allow(dead_code)]
const _: () = {
    fn assert_send<T: ?Sized + Send>() {}
    fn assert<T: ?Sized + Send>() {
        assert_send::<Locked<T>>();
    }
};

assert_impl_all!(Lock: Sync);

// SAFETY: - We've asserted above that Lock is Sync.
//         - The phantom field only exists so that we don't accidentally implement Sync.
//         - Locked only gives access to one thread at a time, meaning that Sync can be
//           modeled as transferring ownership every time the accessing thread changes.
unsafe impl<T> Sync for Locked<T> where T: ?Sized + Send {}

// SAFETY: - If T: Sync, then `Locked<T>` is just a glorified `T`.
// https://github.com/rust-lang/rust/issues/29864
// unsafe impl<T> Sync for Locked<T> where T: ?Sized + Sync {}

impl<T> Deref for Locked<T>
where
    T: ?Sized,
{
    type Target = Lock;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.lock
    }
}

impl Lock {
    /// Wraps a value in a [`Locked`] protected by this lock.
    ///
    /// This function clones the [`Lock`] which makes it about as expensive as cloning an
    /// [`Arc`]. Note that this is much more expensive than creating an ordinary mutex.
    ///
    /// # Example
    ///
    /// ```
    /// use shared_lock::Lock;
    ///
    /// let lock = Lock::default();
    /// let locked = lock.wrap(5);
    /// let guard = &lock.lock();
    /// assert_eq!(*locked.get(guard), 5);
    /// ```
    #[inline]
    pub fn wrap<T>(&self, value: T) -> Locked<T> {
        Locked {
            lock: self.clone(),
            _phantom_not_sync: Default::default(),
            value: UnsafeCell::new(value),
        }
    }
}

impl<T> Locked<T>
where
    T: ?Sized,
{
    /// Accesses the locked value.
    ///
    /// The guard must be a guard created from the same [`Lock`] that was used to create
    /// this object. That is the same [`Lock`] that this object [`Deref`]s to.
    ///
    /// This function performs only a single comparison and a jump, which makes it very
    /// fast and suitable for inner loops.
    ///
    /// # Panic
    ///
    /// Panics if the guard was not created from the same [`Lock`] that was used to create
    /// this object.
    ///
    /// # Example
    ///
    /// ```
    /// use shared_lock::Lock;
    ///
    /// let lock = Lock::default();
    /// let locked1 = lock.wrap(5);
    /// let locked2 = lock.wrap(6);
    /// let guard = &lock.lock();
    /// assert_eq!(*locked1.get(guard), 5);
    /// assert_eq!(*locked2.get(guard), 6);
    /// ```
    #[inline]
    pub fn get<'a>(&'a self, guard: &'a Guard) -> &'a T {
        assert_not_impl_any!(Guard<'_>: Sync, Send);
        assert!(
            self.lock.is_locked_by(guard),
            "guard does not guard this object",
        );
        // SAFETY: - It is clear that self.value is valid for the lifetime 'a
        //         - The only thing to consider is T: !Sync and T: Send since this implies
        //           Locked<T>: Sync.
        //         - Since Guard: !Sync and Guard: !Send, and only one execution unit at
        //           a time can lock self.lock, no other execution unit can have a guard
        //           for self.lock.
        //         - We only hand out references to the value here and in get_mut, but
        //           since this function takes &self, no reference returned by get_mut can
        //           be alive.
        //         - Since all of these references handed out by this function borrow
        //           their guards, and no other execution unit has a guard for self.lock,
        //           no other execution unit can have a reference to the value.
        //         - Therefore returning this reference for the problematic T: !Sync but
        //           T: Send can be modeled as first moving ownership to this execution
        //           unit.
        unsafe { &*self.value.get() }
    }

    /// Unwraps the value, consuming this object.
    ///
    /// # Examples
    ///
    /// ```
    /// use shared_lock::Lock;
    ///
    /// let lock = Lock::default();
    /// let locked = lock.wrap(5);
    /// assert_eq!(locked.into_inner(), 5);
    /// ```
    #[inline]
    pub fn into_inner(self) -> T
    where
        T: Sized,
    {
        self.value.into_inner()
    }

    /// Returns a mutable reference to the contained value.
    ///
    /// # Examples
    ///
    /// ```
    /// use shared_lock::Lock;
    ///
    /// let lock = Lock::default();
    /// let mut locked = lock.wrap(5);
    /// *locked.get_mut() = 6;
    /// assert_eq!(locked.into_inner(), 6);
    /// ```
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        self.value.get_mut()
    }

    /// Returns a pointer to the underlying value.
    ///
    /// # Examples
    ///
    /// ```
    /// use shared_lock::Lock;
    ///
    /// let lock = Lock::default();
    /// let locked = lock.wrap(5);
    /// // SAFETY: locked hasn't been shared with any other thread.
    /// unsafe {
    ///     assert_eq!(*locked.data_ptr(), 5);
    /// }
    /// ```
    #[inline]
    pub fn data_ptr(&self) -> *const T {
        self.value.get()
    }
}

impl<T> Debug for Locked<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Locked")
            .field("lock_id", &self.lock.addr())
            .field(
                "value",
                &debug_fn(|fmt| {
                    if let Some(guard) = self.lock.try_lock() {
                        Debug::fmt(self.get(&guard), fmt)
                    } else {
                        fmt.write_str("<locked>")
                    }
                }),
            )
            .finish_non_exhaustive()
    }
}
