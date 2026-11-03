//! The constructor that records which standard descriptors were closed at
//! start-up, and its proof (ADR-2026-11-02-2253, ADR-2026-11-03-0808).
//!
//! Verus proves `record_slots` against #117's specification: afterwards,
//! slot `fd` of `CLOSED` holds the OS error that `fcntl(fd, F_GETFD)` failed
//! with, for `fd` in 0 to 2, and 0 when it did not fail with one. Verus also
//! proves that every index is in bounds and that nothing panics.
//!
//! Verus cannot check a foreign function, a link section, or the value that
//! a standard-library atomic holds. Each of those sits behind one item
//! marked TRUSTED, whose specification Verus assumes without proof. They
//! are the trusted base that ADR-2026-11-03-0808 lists, and the
//! `unsafe-code` check rejects any other unsafe code or assumption.

#![allow(unsafe_code)]

use std::ffi::c_int;
use std::sync::atomic::Ordering;

use vstd::prelude::*;

/// `F_GETFD` of `<fcntl.h>`: 1 on every target this module is built for.
const F_GETFD: c_int = 1;

// TRUSTED: POSIX's `int fcntl(int fildes, int cmd, ...)`, which the C
// library of every target this module is built for provides. Verus cannot
// take a variadic foreign function; only `getfd` calls it.
unsafe extern "C" {
    fn fcntl(fd: c_int, cmd: c_int, ...) -> c_int;
}

verus! {

/// What `fcntl(fd, F_GETFD)` returned when `record` called it.
pub uninterp spec fn getfd_result(fd: int) -> c_int;

/// The OS error that `fcntl(fd, F_GETFD)` left in `errno` when it failed,
/// as `io::Error::raw_os_error` gives it.
pub uninterp spec fn getfd_error(fd: int) -> Option<i32>;

/// What slot `fd` of `CLOSED` must hold once `record` has run: the OS error
/// of `fcntl(fd, F_GETFD)` when it failed with one, and 0 otherwise.
pub open spec fn recorded(fd: int) -> i32 {
    if getfd_result(fd) == -1 {
        match getfd_error(fd) {
            Some(code) => code,
            None => 0,
        }
    } else {
        0
    }
}

/// TRUSTED: calls `fcntl(fd, F_GETFD)`. Verus assumes that it returns
/// without panicking and writes no memory that the program owns: its
/// signature lets it change nothing that Verus tracks. `F_GETFD` only reads
/// the descriptor's flags, and on a descriptor that is not open it fails
/// with `EBADF`. Its result may be any `c_int`, named `getfd_result(fd)`.
#[verifier::external_body]
fn getfd(fd: c_int) -> (result: c_int)
    ensures
        result == getfd_result(fd as int),
    no_unwind
{
    // SAFETY: `F_GETFD` takes no third argument. On a descriptor that is
    // not open it fails with `EBADF`, and changes nothing.
    unsafe { fcntl(fd, F_GETFD) }
}

/// TRUSTED: the OS error of the last failed call into the C library on this
/// thread. Called right after `getfd(fd)` returned -1, with no call between
/// that could set `errno`, it is the error of that call.
#[verifier::external_body]
fn last_error(Ghost(fd): Ghost<int>) -> (code: Option<i32>)
    requires
        getfd_result(fd) == -1,
    ensures
        code == getfd_error(fd),
    no_unwind
{
    std::io::Error::last_os_error().raw_os_error()
}

/// TRUSTED: a ghost view of the three slots of `CLOSED`. Verus cannot see
/// the value of a standard-library atomic: vstd's specification of
/// `AtomicI32` says nothing of it. So this token stands for the slots, and
/// `holds` says what each one holds. Only `take_slots` makes one and only
/// `store` changes one. Erased: it does not exist in the built crate.
#[verifier::external_body]
pub tracked struct Slots {
    _private: (),
}

impl Slots {
    /// What slot `fd` of `CLOSED` holds.
    pub uninterp spec fn holds(&self, fd: int) -> i32;
}

/// TRUSTED, the `.init_array` contract: the C runtime calls `record` once,
/// on the main thread, before `main` and before any other thread exists. So
/// while `record` runs, it alone reads and writes `CLOSED`, and it may hold
/// the view of its slots. Verus assumes nothing of what they hold.
axiom fn take_slots() -> (tracked slots: Slots);

/// TRUSTED: stores `code` in slot `fd` of `CLOSED`. Afterwards that slot
/// holds `code`, and every other slot holds what it held.
#[verifier::external_body]
fn store(fd: usize, code: i32, Tracked(slots): Tracked<&mut Slots>)
    requires
        fd < 3,
    ensures
        final(slots).holds(fd as int) == code,
        forall|i: int| i != fd ==> #[trigger] final(slots).holds(i) == old(slots).holds(i),
    no_unwind
{
    super::CLOSED[fd].store(code, Ordering::Relaxed);
}

/// Stores in each slot of `CLOSED` the error of its descriptor, or 0: the
/// loop that Verus proves against #117's specification.
fn record_slots(Tracked(slots): Tracked<&mut Slots>)
    ensures
        forall|fd: int| 0 <= fd < 3 ==> #[trigger] final(slots).holds(fd) == recorded(fd),
    no_unwind
{
    // A `while` loop: vstd's specification of iterators, which a `for` loop
    // uses, allows them to panic.
    let mut fd: usize = 0;
    while fd < 3
        invariant
            fd <= 3,
            forall|i: int| 0 <= i < fd ==> #[trigger] slots.holds(i) == recorded(i),
        decreases 3 - fd,
    {
        let code = if getfd(fd as c_int) == -1 {
            last_error(Ghost(fd as int)).unwrap_or(0)
        } else {
            0
        };
        store(fd, code, Tracked(slots));
        fd += 1;
    }
}

/// Records the error of each standard descriptor that is closed. It runs
/// from `.init_array`, before the standard library's start-up code opens
/// `/dev/null` on them.
extern "C" fn record()
    no_unwind
{
    let tracked mut slots = take_slots();
    record_slots(Tracked(&mut slots));
}

} // verus!

// TRUSTED, the `.init_array` contract. SAFETY: the C runtime calls each
// function in `.init_array` once, on the main thread, before `main`, with
// the C calling convention. `record` has it, takes no argument that it
// reads, and only calls `fcntl`, reads `errno` and stores to atomics, none
// of which needs the standard library's start-up code. Some C runtimes pass
// `argc`, `argv` and `envp` to these functions and others pass nothing; a C
// function may ignore its arguments, since the caller owns and cleans them
// up.
#[used]
#[unsafe(link_section = ".init_array")]
static RECORD: extern "C" fn() = record;
