# A native run that outgrows its stack makes its differential test invalid

Status: accepted
Tier: implementation; area: testing-and-harness

## Context

A built executable that outgrows its stack exits with 2 and writes one
line, `PROGRAM: @f ran out of the N bytes of stack reserved for it`
(ADR-2026-11-02-1132). `tools.native_values` read that as any other
failure, so a differential test where `fir-ref` returns failed with
`native code fails where fir-ref returns`, as ADR-2026-11-02-2250 kept it.

[#172](https://github.com/pmatos/funk/issues/172) drops the cap of 20
calls on differential recursion, and asks that a run deeper than its
stack report the stack message and not count as a mismatch. fir has no
depth limit (ADR-2026-10-30-1549), so a stack that is too small says
nothing about the code. A miscompiled recursion that never ends also ends
at the guard page, so a verdict that passes would hide a real bug.

## Decision

- `tools.native_values` returns `refine.OutOfStack(N)` for exit status 2,
  empty standard output, and exactly that one line on standard error.
  Anything else, such as `cannot reserve N bytes of stack for @f`, stays
  a failure.
- An `OutOfStack` run makes its test **invalid**, after the checks of
  `fir-ref`'s own result, with `native code outgrew its N bytes of stack`.
  This is the mirror of `fir-ref` running out of fuel: the run proves
  nothing, and invalid counts as a failure, so the harness stays red.
- `scripts/harness/fixtures/out-of-stack/` holds one such test, 1,000,000
  calls deep. `check_invalid.py` runs the harness on it under an 8 MiB
  stack limit, and passes only when the harness reports it invalid for
  that reason.

## Alternatives

- **A passing verdict, or a sidecar key that declares the overflow.** A
  pass hides a runaway recursion, and a new key widens the corpus format
  for one test.
- **A failure, as before.** That is the mismatch #172 forbids.
- **Pin `ulimit -s` for every native run of the harness.** A separate
  decision; here only the fixture's run needs a known stack.

## Consequences

- A corpus test that outgrows the stack of the machine that runs it is
  reported invalid, with the bytes that it had. Its fix is a shallower
  test or a larger `ulimit -s`.
- ADR-2026-11-02-2250's "the verdicts do not change" and
  ADR-2026-11-02-1132's "a failure where `fir-ref` returns" now hold for
  every native failure but this one.
- The corpus's deep tests assume the default 8 MiB stack: `@deep` at
  `i8` and `i64` take 80 bytes a level and fit 100,000 calls with about
  4% to spare, and `@scale` at `i128` takes 144 bytes and fits 50,000.
  Frames that grow in M1 or M2 turn those tests invalid until they are
  made shallower.
