# `fir-ref run FILE @FUNC ARG...` runs one function and prints its result as one JSON object

Status: accepted

## Context

[#10](https://github.com/pmatos/funk/issues/10) asks for
`fir-ref run <file.fir> @func <args...>`, which runs a function with the
spec's interpreter and prints a JSON result: the returned values, each a
value or poison; UB with a reason; fuel exhausted; or stuck. Arguments and
values are spelled as constants are in text. The harness of
[#13](https://github.com/pmatos/funk/issues/13) compares this result with
what a native executable prints, `{"values":["V1","V2"]}`
(ADR-2026-10-30-1233), and sets a fuel budget for each test. `fir-ref`
follows `funk`'s command line (ADR-2026-10-30-1425).

Until #14 gives `freeze` its choice, a run has one path, so it has one
result.

## Decision

- **Command.** `fir-ref run [--fuel N] FILE @FUNC [ARG...]` parses FILE
  with the core dialect, without validating it, and runs the function
  `Func.run` on the arguments, in a monad with one path. A FILE of `-` is
  standard input, and `--` ends the options.
- **The function.** `@FUNC` is the function's symbol as fir's text writes
  it, quoted exactly when it is not a word: `@add3`, `@"a b"`, as in
  ADR-2026-10-30-1233.
- **Arguments.** One per parameter, each spelled as a `const` of the
  parameter's type is in text: `true` or `false` at `i1`, and signed
  decimal at every other width, with no leading zeros, no `+` and no `-0`,
  in the type's range. `fir-ref` reads each one with the spec's lexer and
  `Core.Op.decode`. `poison` is a value of every `iN`, since the runs of a
  function include poison arguments (`Core.FuncRuns`). `ptr` has no values.
- **Fuel.** N steps, one for each op the run runs, its terminators
  included. N is decimal; its default is 1,000,000.
- **Output.** One JSON object on one line of standard output, with a
  `kind`:
  - `{"kind":"return","values":["V1","V2"]}`: the returned values in order,
    each a string spelled as the arguments are, or `"poison"`. A function
    with no result prints `"values":[]`.
  - `{"kind":"ub","reason":"..."}`: immediate UB.
  - `{"kind":"fuel-exhausted"}`: the run used all its fuel.
  - `{"kind":"stuck","reason":"..."}`: the run reached a case that
    validation rules out.

  Strings escape as `fir-ref validate`'s and `funk`'s reports escape them
  (ADR-2026-10-30-1032). Reasons are for people: tools compare the kind
  and the values only.
- **Exit status.** 0 for `return`, `ub` and `fuel-exhausted`. 1 for
  `stuck`, and for a text that does not parse, which prints
  `FILE:LINE:COL: parse error: REASON` on standard error and nothing on
  standard output, as `fir-ref fmt` does. 2, with one line on standard
  error and nothing on standard output, for a usage or I/O error, a
  function the module does not have, a wrong number of arguments, an
  argument that is not a value of its type (`fir-ref: 128 is not a value
  of type i8`) and an op without execution rules (ADR-2026-10-30-1855).
  Text from the command line shows each control character, below 0x20 or
  0x7f, as `\xHH`, so that a message stays on one line.

## Alternatives

- **Bare JSON numbers.** `i1` would read as booleans, and wide values lose
  precision in many JSON readers (ADR-2026-10-30-1233).
- **Exit status 0 for stuck.** Stuck shows that the module is not valid,
  which `funk`'s tools report with status 1.
- **No fuel option.** #13 sets a budget for each test, and a test that
  expects fuel exhausted needs a budget smaller than its run.

## Consequences

- #13 compares `values` with a native executable's `values` position by
  position, with no translation: `"poison"` matches any native value.
- A test with poison arguments is interpreter-only: a native executable
  takes no `poison`.
- #14's exhaustive mode prints a set of results; it extends this output in
  its own ADR.
