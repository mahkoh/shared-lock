# shared-lock

[![crates.io](https://img.shields.io/crates/v/shared-lock.svg)](https://crates.io/crates/shared-lock)
[![docs.rs](https://docs.rs/shared-lock/badge.svg)](https://docs.rs/shared-lock)
![MSRV](https://img.shields.io/crates/msrv/shared-lock)

The shared-lock crate provides a re-entrant lock that can be used to lock
multiple disconnected objects such as in the following example:

```rust
struct Context {
    lock: Lock,
    data1: Locked<Cell<u32>>,
}

struct Child {
    context: Arc<Context>,
    data2: Locked<Cell<u32>>,
}
```

Both objects in this example implement `Sync` because `Locked<T>: Sync` if
`T: Send`.

After the lock has been locked once in a thread, locking it again is about as
expensive as cloning an `Rc` and accessing the locked fields is essentially
free.

## Safety

This crate has 100% test coverage generated through mutation testing
and all tests are run through miri.

## MSRV

The MSRV is `max(1.85, stable - 3)`.

## License

This project is licensed under either of

- Apache License, Version 2.0
- MIT License

at your option.
