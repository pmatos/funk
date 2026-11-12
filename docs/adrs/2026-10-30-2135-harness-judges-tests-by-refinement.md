# The harness judges a differential test by refinement over its set of outcomes: UB and fuel exhausted make it invalid, and stuck or a tool error fails it

Status: accepted
Tier: direction; area: testing-and-harness

## Decision

The harness reports each test as passed, failed or invalid. An invalid test
never counts as a pass, and it fails the run.

- **A differential test** runs on `fir-ref` in exhaustive mode, at its fuel
  budget and a choice budget of 16 bits, and as native code from `funk build`.
  Native code passes when its values refine one outcome of the set: the lists
  have the same length, and each value is equal, or any value of its type where
  `fir-ref` gives poison.
- A stuck path fails the test, even in a set that also holds UB. Otherwise UB,
  or fuel exhausted, anywhere in the set makes it invalid. A tool error fails
  it: `fir-ref` exiting with 2, an executable that exits with 2 or dies by a
  signal, or a module that `funk build` does not build. UB reasons are never
  compared.
- **Declared results.** A test may declare `results`, each with its values and
  a witness choice sequence that must give exactly them. Within the budget, the
  set must be exactly the declared results. Past it, a test that declares none
  is invalid. A test that declares results runs seeds 0 to 31 in sampled mode,
  each of which must give a declared result, and native code passes when its
  values refine one declared result.
- **An interpreter-only test** passes when `fir-ref` gives the expected result:
  the same values, poison included, UB with any reason, or fuel exhausted. It
  may name its path with `choices`; without it, a run that chooses fails.

## Why

`freeze` of poison makes a run's behaviour a set of outcomes, and correctness
is refinement (ADR-2026-10-29-2017, ADR-2026-10-29-2008). Source UB allows any
result, so a test that reaches it proves nothing about native code. A run out
of fuel depends on the budget, not on either tool. No run of a valid module is
stuck (`NeverStuck`), so stuck is a bug.

## Rejected alternatives

- **Fuel exhausted as a pass, or as a failure.** It says nothing about native
  code, and neither tool is wrong: the test is.
- **Compare UB reasons.** Refinement ignores them, and the tools need not word
  them alike.
- **Sample on every declared test.** Within the budget the set is exact.
- **A per-test choice budget.** The budget bounds the harness's cost; a test
  past it declares its results.
- **Fail rather than invalidate a sampled UB.** A sampled outcome is a member of
  the set.
