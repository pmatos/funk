//! `funk-start-fds`: which of the standard file descriptors, 0 to 2, were
//! closed when the process started (ADR-2026-11-02-2253).
//!
//! Before `main` runs, Rust's standard library opens `/dev/null` on each of
//! them that is closed, so `main` cannot tell a closed standard input from
//! an empty one, nor a closed standard output from one that takes every
//! write. On ELF Unix targets, one constructor in `.init_array` looks at
//! them first and records what it finds. It is the only unsafe code in the
//! workspace, and Verus proves it (ADR-2026-11-03-0808). On every other
//! target it compiles out, and every descriptor reads as open.

// Cargo does not pass [lints] to doctests (ADR-2026-11-03-0808).
#![doc(test(attr(forbid(unsafe_code))))]

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
/// calls: all of the crate's unsafe code, which Verus proves
/// (ADR-2026-11-03-0808).
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
mod record;
