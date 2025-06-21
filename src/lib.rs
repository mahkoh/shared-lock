//! This crate provides the [`Lock`] and [`Locked`] types which allow one lock to guard
//! multiple objects.
//!
//! # Motivation
//!
//! The following pattern is common in languages such as C and Java:
//!
//! ```c
//! struct Context {
//!     mutex_t mutex;
//!     int protected_data1;
//! };
//!
//! struct Child {
//!     struct Context *context;
//!     int protected_data2;
//! };
//! ```
//!
//! Here, `protected_data1` and `protected_data2` are protected by the same mutex.
//! Whenever the code wants to access either of those fields, it first locks the mutex.
//!
//! Since there is only one mutex, this provides the following properties:
//!
//! 1. The code does not need to reason about locking order to avoid deadlocks.
//! 2. Only one expensive atomic RMW operation has to be performed to access all fields.
//!
//! Using common Rust data structures, this might be modeled as follows:
//!
//! ```
//! use std::cell::Cell;
//! use std::sync::Arc;
//! use parking_lot::{Mutex, ReentrantMutex};
//!
//! struct Context {
//!     mutex: Mutex<()>,
//!     protected_data1: ReentrantMutex<Cell<i32>>,
//! }
//!
//! struct Child {
//!     context: Arc<Context>,
//!     protected_data2: ReentrantMutex<Cell<i32>>,
//! }
//! ```
//!
//! The code would then acquire the mutex at a very high level and acquire the reentrant
//! mutexes ad-hoc whenever a field needs to be accessed.
//!
//! This achieves the first property of not having to reason about the lock order, but
//! it does not achieve the second property.
//!
//! This crate improves on this by providing data structures that follow the C model
//! closely.
//!
//! # Example
//!
//! Using the data structures from this crate, the example above could be implemented as
//! follows:
//!
//! ```
//! use std::cell::Cell;
//! use std::sync::Arc;
//! use shared_lock::{Lock, Locked};
//!
//! struct Context {
//!     lock: Lock,
//!     protected_data1: Locked<Cell<i32>>,
//! }
//!
//! struct Child {
//!     context: Arc<Context>,
//!     protected_data2: Locked<Cell<i32>>,
//! }
//!
//! // Constructing the objects:
//! let lock = Lock::default();
//! let context = Arc::new(Context {
//!     protected_data1: lock.wrap(Cell::new(0)),
//!     lock,
//! });
//! let child = Arc::new(Child {
//!     context: context.clone(),
//!     protected_data2: context.lock.wrap(Cell::new(0)),
//! });
//!
//! // Accessing the objects:
//! let guard = &context.lock.lock();
//! context.protected_data1.get(guard).set(1);
//! child.protected_data2.get(guard).set(1);
//! ```
//!
//! [`Lock`] is a re-entrant lock. If it has not yet been acquired, calling [`Lock::lock`]
//! is about as expensive as acquiring a regular mutex. If it has already been acquired by
//! the current thread, calling [`Lock::lock`] is about as expensive as cloning an [`Rc`].
//!
//! [`Locked::get`] only performs a single non-atomic comparison before returning a
//! reference to the contained object, making it effectively free in most situations.
//!
//! Since [`Locked::get`] can be called any number of times, it only returns a shared
//! reference. The contained data must use interior mutability to be mutated. However,
//! [`Locked`] implements [`Sync`] as long as the contained type implements [`Send`],
//! meaning that the contained type can use cheap non-atomic interior mutability such as
//! [`Cell`] and [`RefCell`].

#[cfg(doc)]
use std::{
    cell::{Cell, RefCell},
    rc::Rc,
};
pub use {
    lock::{Guard, Lock},
    locked::Locked,
};

mod execution_unit;
mod lock;
mod locked;
