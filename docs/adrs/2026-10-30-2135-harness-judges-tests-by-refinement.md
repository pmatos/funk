# The harness judges a differential test by refinement: UB and fuel exhausted make it invalid, and stuck or a tool error fails it

Status: accepted

## Context

The differential harness of
[#13](https://github.com/pmatos/funk/issues/13) runs each test of the
corpus on `fir-ref run` and, for a differential test, as native code from
`funk build` (ADR-2026-10-30-2049). It reports each test as passed, failed
or invalid, and an invalid test never counts as a pass.

- Correctness is refinement: the native result must refine `fir-ref`'s,
  and a poison result is refined by any value (ADR-2026-10-29-2008). A
  function returns a list of values, any number of them
  (ADR-2026-10-30-0816).
- `fir-ref run` gives one of four results: the returned values, UB with a
  reason, fuel exhausted, or stuck (ADR-2026-10-30-1856). An executable
  prints its values, or exits with 2 or dies by a signal
  (ADR-2026-10-30-1233).
- ADR-2026-10-29-2017 leaves open how the harness treats fuel exhausted,
  and says #13 records it. Comment 6507458782 on #13 does.
- No run of a valid module is stuck (`NeverStuck`).
- UB reasons are for people: refinement ignores them (#13).

## Decision

- **A differential test** is judged on `fir-ref`'s result:
  - Values: both lists have the same length, and each native value equals
    `fir-ref`'s, or is any value of its result type where `fir-ref`
    returns poison. The harness reads the result types from the function's
    signature line in the canonical text. A match passes the test, and
    anything else fails it.
  - UB makes the test invalid: source UB allows any result.
  - Fuel exhausted makes the test invalid too: the result depends on the
    budget. The author raises the test's fuel budget, or makes it an
    interpreter-only test that expects fuel exhausted.
  - Stuck fails the test.
  - A tool error fails the test: `fir-ref` exits with 2 (such as an op
    without execution rules, ADR-2026-10-30-1855), the executable exits
    with 2 or dies by a signal, or `funk build` does not build the module.
- **An interpreter-only test** passes when `fir-ref` gives the expected
  result: the same values, poison included, or UB with any reason, or
  fuel exhausted. Stuck, or any other result, fails it.

## Alternatives

- **Fuel exhausted as a pass.** The run stopped before a result, so it
  says nothing about what native code returns.
- **Fuel exhausted as a failure.** Neither tool is wrong; the test is. An
  invalid test fails the run all the same, and its line says what the
  author changes.
- **Compare UB reasons.** Refinement ignores them, and the two tools need
  not word them alike.

## Consequences

- The tracer subset gives no poison and no UB, so until #14 only the
  unit tests of `scripts/harness/refine.py` reach those branches.
- #14's sets of outcomes and #31's several native values extend
  `refine.py` and `tools.py`.
- The signature reader knows the canonical text, not every dialect: a type
  written with a string that holds a parenthesis would confuse it. Core
  types have none.
