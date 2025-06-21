#[cfg(test)]
mod tests;

/// Returns the ID of the current execution unit.
///
/// The returned ID is never 0. There are therefore usize::MAX - 1 different execution
/// units.
///
/// At any time, an execution unit is either active or inactive. It is active if there is
/// a thread such that this function returns the ID of the execution unit and inactive
/// otherwise.
///
/// If there are two threads such that this function returns the same ID in both threads,
/// then the termination of one of the threads happens before the start of the other
/// thread.
///
/// # Informal explanation
///
/// An execution unit is morally a single thread except that it might span across multiple
/// threads that are connected by a happens-before relationship.
///
/// This become relevant when
///
/// 1. a thread locks the mutex
/// 2. forgets the guard
/// 3. terminates
/// 4. another thread starts and re-uses the thread-local storage, getting the same
///    execution ID
/// 5. eventually unlocks the mutex
///
/// We allow this because it makes reasoning about safety easier because there are fewer
/// special cases to consider. We invent the "execution unit" terminology because we don't
/// want to spell this out every time.
#[inline(always)]
pub(crate) fn execution_unit_id() -> usize {
    thread_local!(static EXECUTION_UNIT_ID: u8 = const { 0 });
    EXECUTION_UNIT_ID.with(|id| {
        let id: *const u8 = id;
        id as usize
    })
}
