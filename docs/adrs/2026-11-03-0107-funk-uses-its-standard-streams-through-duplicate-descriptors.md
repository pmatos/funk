# funk reads and writes its standard streams through files on duplicates of their descriptors

Status: accepted; refined by ADR-2026-11-09-1540

## Context

ADR-2026-10-30-1032 says funk reports input it cannot read as an I/O
error, and that when it cannot write its output it says so on standard
error and exits with 2. `fir-ref` does this for every standard stream it
cannot use.

Rust's standard library hides one error. Its handles `std::io::stdin()`,
`stdout()` and `stderr()` take `EBADF` for the end of the input and for a
successful write (`handle_ebadf` in `library/std/src/io/stdio.rs`, Rust
1.99.1). A descriptor open in the wrong mode gives `EBADF` on every read or
write. So funk read a standard input open only for writing as an empty
text, a parse error with exit 1. It lost its output on a standard output
open only for reading, and exited with its verdict. It also exited with its
verdict when it could not write a diagnostic to a standard error open only
for reading. `fir-ref` exits with 2 in each case
([#104](https://github.com/pmatos/funk/issues/104)).

A closed standard error hid the same failure another way. Before `main`,
the standard library opens `/dev/null` on each standard descriptor that is
closed, so the diagnostic went there and funk exited with its verdict,
where `fir-ref` exits with 2.
ADR-2026-11-02-2253 records which standard descriptors were closed when
funk started. funk used that for standard input and output only, and the
ADR said that its behaviour on a closed standard error did not change.

## Decision

- **Through a `File`.** On Unix, funk reaches its standard streams only
  through [`crates/funk/src/streams.rs`](../../crates/funk/src/streams.rs).
  It reads `-` and writes standard output and standard error through a
  `File` on a duplicate of descriptor 0, 1 or 2, made by
  `try_clone_to_owned`, which is safe code. A `File` returns `EBADF` like
  any other error.
- **Buffered as before.** Standard output is a `LineWriter`, as the
  standard library's is, and standard error is not buffered. On a
  descriptor open in the right mode, funk makes the same writes, in the
  same order, as before.
- **Closed at start.** A stream that `funk-start-fds` records as closed
  when funk started fails every read and write with `EBADF`. This now
  covers standard error.
- **What funk reports.** A standard input it cannot read is
  `cannot read standard input: ...`, an `io-error` with exit 2. A standard
  output it cannot write ends the run with
  `funk: cannot write standard output: ...` on standard error and exit 2. A
  diagnostic it cannot write to standard error ends the run with exit 2
  and no message. A run that writes nothing to a stream it cannot use exits
  as before, as `fir-ref` does.
- **Elsewhere**, funk keeps the standard library's handles. On Windows they
  write to a console as UTF-16, which a `File` would not do.

## Alternatives

- **Check each descriptor's mode with `fcntl(F_GETFL)`.** It needs a call
  into the C library: more unsafe code, which ADR-2026-11-02-2253 forbids,
  or a third-party crate, which ADR-2026-10-30-1030 does not take yet.
- **A `BufWriter` for standard output.** It would change how standard
  output and standard error interleave when they go to one file.
- **Accept the difference.** #104 asks funk to match `fir-ref`, and
  ADR-2026-10-30-1032 already says to exit with 2.

## Consequences

- funk and `fir-ref` give the same verdicts and exit codes on a standard
  stream open in the wrong mode, and on a closed standard error.
- Code that reads `std::io::stdin()` or writes `std::io::stdout()` or
  `std::io::stderr()` directly brings the difference back. New input and
  output goes through `streams`.
- A panic still prints through the standard library's standard error; it
  exits with 2 in any case.
- funk holds up to three more descriptors than before. Under an open-file
  limit below 6 it reports "Too many open files" where it used to run.
  `fir-ref` fails under a limit below 12, so no comparison sees this.
- A test runs `fmt` on several files with standard output and standard
  error on one file, and checks that their lines come in order. It fails
  if standard output is buffered by more than a line.
