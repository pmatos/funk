# One start-up constructor records closed standard descriptors, the workspace's only unsafe code

Status: superseded by ADR-2026-11-09-1603

## Context

ADR-2026-10-30-1032 says funk reports a file it cannot read as an I/O
error, and says on standard error that it cannot write its output, with
exit 2. `fir-ref` does this for a closed standard input and a closed
standard output. funk did not
([#60](https://github.com/pmatos/funk/issues/60)): it read a closed
standard input as an empty text, a parse error with exit 1. On a closed
standard output it exited with its verdict, 0 or 1, with its output lost.

The cause is Rust's standard library. Before `main` runs, its start-up code
opens `/dev/null` on each of descriptors 0 to 2 that is closed. Inside
`main`, such a descriptor cannot be told apart from `/dev/null` that the
caller opened, as Python's `subprocess.DEVNULL` does. Only code that runs
before the standard library's start-up can see that a descriptor is closed.
Such code needs an unsafe attribute, `#[unsafe(link_section)]`, an
`unsafe extern` block and an `unsafe` call. ADR-2026-10-30-1030 sets
`unsafe_code = "forbid"` for the workspace, and an `allow` cannot lift
`forbid`.

The human ruled (2026-11-02, option 1 on #60, comment 6590317705) for one
scoped exception, to keep funk's verdicts identical to `fir-ref`'s.

## Decision

- **One constructor.** The library crate
  [`crates/funk-start-fds`](https://github.com/pmatos/funk/blob/verus-tooling-m0/crates/funk-start-fds/src/lib.rs) puts one
  function in `.init_array`. It runs before the standard library's start-up
  code, calls `fcntl(fd, F_GETFD)` on descriptors 0, 1 and 2, and stores in
  an atomic the error of each that is closed, `EBADF`.
  `closed_at_start(Stream)` returns it.
- **ELF Unix only.** The constructor is built on Linux, Android, FreeBSD,
  DragonFly, NetBSD, OpenBSD, illumos and Solaris. Elsewhere it compiles
  out, every descriptor reads as open, and funk behaves as before.
- **Lint scope.** Cargo cannot inherit `[workspace.lints]` and change one
  lint. So `funk-start-fds` has its own `[lints]`: `unsafe_code = "deny"`
  and the workspace's other lints. A single `#[allow(unsafe_code)]` sits on
  its module `record`, which holds the `fcntl` declaration, the constructor
  and its `.init_array` entry, each with a `// SAFETY:` comment. Every other
  crate, `funk` included, keeps `workspace = true` and so `forbid`.
- **No other unsafe code.** This module is the only unsafe code in the
  workspace. Nothing else may lower `forbid` or add to the module; another
  exception needs its own ADR and a human ruling. A lint added to
  `[workspace.lints]` is added to `funk-start-fds` too.
- **What funk does with it.** For `-`, `fmt`, `verify` and `build` report a
  closed standard input as `cannot read standard input: ...`, an
  `io-error` with exit 2. Every write to a closed standard output fails,
  so funk prints `funk: cannot write standard output: ...` on standard
  error and exits with 2. A run that writes nothing there exits as before,
  as `fir-ref` does. The flag of standard error is recorded, but funk's
  behaviour on a closed standard error does not change.

## Alternatives

- **Accept the difference**, option 2 of #60: the ruling rejected it.
- **`deny` in the `funk` crate.** `funk` would have to stop inheriting the
  workspace's lints and copy them, and `deny` would cover the whole driver.
- **`#![no_main]` with funk's own C `main`.** It needs more unsafe code and
  drops the standard library's start-up, which sets up `SIGPIPE`.
- **The `ctor` crate.** The same unsafe code from a third party, and
  ADR-2026-10-30-1030 takes no third-party crates yet.
- **Treat `/dev/null` as closed.** It fails callers that pass
  `subprocess.DEVNULL`, such as the harness.

## Consequences

- funk and `fir-ref` give the same verdicts and exit codes on a closed
  standard input or output.
- The unsafe code is one module of one file, reviewed as a whole.
- `funk-start-fds` repeats the workspace's lints and must be kept in step.
- CI tests the behaviour on Linux only; the other targets are not tested.
