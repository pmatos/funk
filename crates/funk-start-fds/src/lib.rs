//! `funk-start-fds`: which of the standard file descriptors, 0 to 2, were
//! closed when the process started (ADR-2026-11-02-2253).
//!
//! Before `main` runs, Rust's standard library opens `/dev/null` on each of
//! them that is closed, so `main` cannot tell a closed standard input from
//! an empty one, nor a closed standard output from one that takes every
//! write. On ELF Unix targets, one constructor in `.init_array` looks at
//! them first and records what it finds. It is the only unsafe code in the
//! workspace. On every other target it compiles out, and every descriptor
//! reads as open.

use std::io;
use std::sync::atomic::{AtomicI32, Ordering};

/// A standard file descriptor.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stream {
    Stdin = 0,
    Stdout = 1,
    Stderr = 2,
}

/// For each standard descriptor, the OS error that it gave when the process
/// started, or 0 when it was open.
static CLOSED: [AtomicI32; 3] = [const { AtomicI32::new(0) }; 3];

/// The error that `stream` gave when the process started, `EBADF`, if it
/// was closed then.
pub fn closed_at_start(stream: Stream) -> Option<io::Error> {
    match CLOSED[stream as usize].load(Ordering::Relaxed) {
        0 => None,
        code => Some(io::Error::from_raw_os_error(code)),
    }
}

/// The constructor, its `.init_array` entry and the one C function it
/// calls: all of the crate's unsafe code.
#[cfg(any(
    target_os = "linux",
    target_os = "android",
    target_os = "freebsd",
    target_os = "dragonfly",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "illumos",
    target_os = "solaris"
))]
#[allow(unsafe_code)]
mod record {
    use std::ffi::c_int;
    use std::sync::atomic::Ordering;

    /// `F_GETFD` of `<fcntl.h>`: 1 on every target this module is built for.
    const F_GETFD: c_int = 1;

    // SAFETY: this is POSIX's `int fcntl(int fildes, int cmd, ...)`, which
    // the C library of every target this module is built for provides.
    unsafe extern "C" {
        fn fcntl(fd: c_int, cmd: c_int, ...) -> c_int;
    }

    /// Records the error of each standard descriptor that is closed. It
    /// runs from `.init_array`, before the standard library's start-up
    /// code opens `/dev/null` on them.
    extern "C" fn record() {
        for (fd, slot) in (0..).zip(&super::CLOSED) {
            // SAFETY: `F_GETFD` only reads the descriptor's flags and takes
            // no third argument. On a descriptor that is not open it fails
            // with `EBADF`, and changes nothing.
            if unsafe { fcntl(fd, F_GETFD) } == -1
                && let Some(code) = std::io::Error::last_os_error().raw_os_error()
            {
                slot.store(code, Ordering::Relaxed);
            }
        }
    }

    // SAFETY: the C runtime calls each function in `.init_array` once, on
    // the main thread, before `main`, with the C calling convention.
    // `record` has it, takes no argument that it reads, and only calls
    // `fcntl`, reads `errno` and stores to atomics, none of which needs the
    // standard library's start-up code. Some C runtimes pass `argc`, `argv`
    // and `envp` to these functions and others pass nothing; a C function
    // may ignore its arguments, since the caller owns and cleans them up.
    #[used]
    #[unsafe(link_section = ".init_array")]
    static RECORD: extern "C" fn() = record;
}
