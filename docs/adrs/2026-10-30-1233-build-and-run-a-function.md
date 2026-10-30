# A built executable runs one function: PROGRAM @FUNCTION ARG... prints {"values":[...]}

Status: accepted

## Context

The differential harness ([#13](https://github.com/pmatos/funk/issues/13))
must call a built function with arguments and read its returned values, to
compare them with `fir-ref`'s. `fir-ref run FILE @func ARGS...` (#10)
spells values as fir constants: `true` and `false` at `i1`, and signed
decimal at every other width. funk reports as text or as JSON lines
(ADR-2026-10-30-1032). Code that funk generates cannot be loaded into a
Rust process: the workspace forbids `unsafe`.

## Decision

- **`funk build [--json] -o OUTPUT FILE`** reads, parses and validates
  `FILE` (`-` is standard input), lowers it, and writes the object file
  `OUTPUT.o` and the executable `OUTPUT` (ADR-2026-10-30-1229). It prints
  nothing when it succeeds. With `--json`, its one report line adds two
  fields, `object` and `executable`, the paths it wrote.
- **New verdicts and kinds.** `unsupported`: the module is valid, but the
  backend cannot lower part of it. Each diagnostic has the fields of a
  validation error (`func`, `block`, `op`, `loc`), and the text form is
  `FILE: unsupported in @f ^block op N: MESSAGE (at @R = LOCATION)`.
  `tool-error`: `as` or `ld` could not run or failed; its message is the
  tool's output. A module that does not parse or validate gets the verdict
  `funk verify` gives it. Exit status: 0 when built; 1 on `parse-error`,
  `validation-error` or `unsupported`; 2 on a usage error, `io-error` or
  `tool-error`.
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
- **Bad command lines.** An unknown function, a wrong number of arguments
  or an argument that is not a value of its type prints one line to
  standard error, such as `PROGRAM: 128 is not a value of type i8`, nothing
  to standard output, and exits with 2. So exit status 2 never means a
  result.
- **How it works.** The entry file holds a runtime in assembly with no
  libc, `crates/funk-x86-64/src/entry/runtime.s`, which uses only the Linux
  system calls `write` and `exit_group`. For each function it adds a
  wrapper, which parses the arguments, calls the function by the System V
  convention (ADR-2026-10-30-1232) and passes each result, sign-extended
  from its width, to the printer, and a table of the functions by their fir
  names.

## Alternatives

- **Call the function from the test process.** Loading generated code
  needs `unsafe`, which the workspace forbids.
- **A generated C `main`.** Readable, but needs a C compiler and libc
  (ADR-2026-10-30-1229).
- **Bare numbers in the JSON list.** `i1` would read as JSON booleans, and
  `i64` values past 2^53 lose precision in many JSON readers.

## Consequences

- #13 runs `funk build`, then the executable once per test, and compares
  the `values` list with `fir-ref`'s. Since `fir-ref`'s JSON is #10's to
  define, #13 maps one shape onto the other.
- A function that crashes, as a division by zero will (#18), ends by a
  signal with nothing on standard output.
- #31 extends the output to several values, as the list already allows.
