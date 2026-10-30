# A built executable runs one function: PROGRAM @FUNCTION ARG... prints {"values":[...]}

Status: accepted

## Context

The differential harness ([#13](https://github.com/pmatos/funk/issues/13))
must call a built function with arguments and read its returned values, to
compare them with `fir-ref`'s. `fir-ref run FILE @func ARGS...` (#10)
spells values as fir constants: `true` and `false` at `i1`, and signed
decimal at every other width. `funk build -o OUTPUT FILE` writes the
executable `OUTPUT` (ADR-2026-10-30-1326). Code that funk generates cannot
be loaded into a Rust process: the workspace forbids `unsafe`. A frame
holds 8 bytes per value (ADR-2026-10-30-1230), so a function with a million
values needs more stack than the 8 MiB that Linux gives a process by
default.

## Decision

- **The executable runs one function.** `OUTPUT @FUNCTION ARG...` names
  the function as fir's text writes it, quoted when it is not a word
  (`@add3`, `@"a b"`), and gives one argument per parameter. Each argument
  is the spelling of a constant of its parameter's type: `true` or `false`
  at `i1`; otherwise signed decimal with no leading zeros, no `+` and no
  `-0`, in the type's range.
- **Output.** On success it writes one line to standard output,
  `{"values":["V1","V2"]}`, a JSON list of the returned values in order,
  each a string with the same spelling, and exits with 0. A function with
  no result prints `{"values":[]}`. Strings keep wide values exact for any
  JSON reader.
- **Errors.** An unknown function, a wrong number of arguments, an argument
  that is not a value of its type, or a stack that cannot be reserved
  prints one line to standard error, such as
  `PROGRAM: 128 is not a value of type i8`, nothing to standard output, and
  exits with 2. Text from the command line (the program's path, the
  function's name, an argument) shows each control byte, below 0x20 or
  0x7f, as `\xHH`, so the message stays on one line. A failed write to
  standard output also exits with 2, with no message; the executable
  ignores `SIGPIPE`, so a reader that closed the pipe gives that status,
  not a signal. So exit status 2 never means a result.
- **A stack of its own.** The function runs on a stack that the runtime
  reserves for it. The table of functions records the bytes each one
  needs: its frame and its wrapper's, each with a return address and a
  saved `%rbp`, the arguments on the stack, and 16 KiB for the runtime's
  routines, rounded up to a page. The runtime maps that with `mmap`
  (`MAP_NORESERVE`, so pages that are never touched cost nothing), makes
  the page below it a guard page, and calls the wrapper with `%rsp` at its
  top. So the process's stack limit (`ulimit -s`) does not bound a frame;
  the backend's 2 GiB does (ADR-2026-10-30-1230). When the stack cannot be
  reserved, as under a low `ulimit -d`, the message is
  `PROGRAM: cannot reserve N bytes of stack for @f`.
- **How it works.** The entry file holds a runtime in assembly with no
  libc, `crates/funk-x86-64/src/entry/runtime.s`, which uses only the Linux
  system calls `write`, `mmap`, `mprotect`, `rt_sigaction` and
  `exit_group`. For each function it adds a wrapper, which parses the
  arguments, calls the function by the System V convention
  (ADR-2026-10-30-1232) and passes each result, sign-extended from its
  width, to the printer, and a table of the functions by their fir names.

## Alternatives

- **Call the function from the test process.** Loading generated code
  needs `unsafe`, which the workspace forbids.
- **A generated C `main`.** Readable, but needs a C compiler and libc
  (ADR-2026-10-30-1229).
- **Bare numbers in the JSON list.** `i1` would read as JSON booleans, and
  `i64` values past 2^53 lose precision in many JSON readers.
- **Run on the process's stack, and check `getrlimit` first.** The check
  cannot know how much of the limit the arguments and the environment
  already use, and with no limit the bound is wherever other mappings
  start. A frame larger than the limit could never run.
- **Run on the process's stack, and report the overflow** from a `SIGSEGV`
  handler on an alternate stack. A clear message, but the frame still
  could not run.

## Consequences

- #13 runs `funk build`, then the executable once per test, and compares
  the `values` list with `fir-ref`'s. Since `fir-ref`'s JSON is #10's to
  define, #13 maps one shape onto the other.
- A function that crashes, as a division by zero will (#18), ends by a
  signal with nothing on standard output.
- A run touches only the pages of its stack that its frames use.
- Calls ([#20](https://github.com/pmatos/funk/issues/20)) make the stack a
  function needs depend on its callees, and with recursion on its
  arguments. #20 must say how the table's figure covers them, and what a
  run that outgrows its stack reports. Until then the guard page turns an
  overflow into a crash, never into a write past the stack.
- #31 extends the output to several values, as the list already allows.
