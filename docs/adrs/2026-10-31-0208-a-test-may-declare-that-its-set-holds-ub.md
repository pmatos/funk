# A differential test may declare that its set holds UB, and then passes only when the harness judges it invalid for that reason

Status: accepted

## Context

ADR-2026-10-31-0003 makes a differential test invalid when UB is in its
set of outcomes, and the harness counts an invalid test as a failure: the
run exits with 1 (ADR-2026-10-30-2049). Until now only a unit test on a
hand-built set, with stand-ins for the tools, checked that rule.
[#18](https://github.com/pmatos/funk/issues/18) asks for a real test of
it: a differential test with a frozen divisor that can be zero is reported
invalid. Put in the corpus as it is, that test fails every run of the
harness, so CI stays red. Kept out, it shows nothing.

## Decision

- **The key.** A differential test may have `invalid = "ub"`: the test
  declares that it is invalid because its set holds UB. `"ub"` is its
  only value. It goes with neither `expect` nor `results`.
- **The run.** The harness runs the test as every differential test:
  `funk build` builds the module, exhaustive mode lists the set, native
  code runs, and ADR-2026-10-31-0003 judges it.
- **The judgement.** The test passes when `funk build` built the module,
  exhaustive mode listed a set that holds UB, and that made the test
  invalid. Anything else fails it: a pass, a failure, invalid for fuel
  exhausted or for a budget exceeded, or a module that does not build.
  Its report line ends with `(declared invalid)` and says why the test is
  invalid, with `fir-ref`'s reason.
- **Every other test** is judged as before. A test without the key that is
  invalid still fails the run.
- **The test.** `tests/fir/canonical/div-frozen.fir` holds #18's: `sdiv`
  at `i8` of 7 by `freeze` of a poison, which may choose 0, so the set
  holds `sdiv by zero`.
- `corpus.py` reads the key and `sets.declared_invalid` judges it.

## Alternatives

- **A harness test on a fixture, run with the real tools.** The
  `fir-harness-test` hook runs the unit tests without building `fir-ref`
  or `funk`, so the test would need a second program that
  `scripts/check-harness.sh` runs, and a fixture corpus of its own,
  must-reject texts included, to load.
- **Run a fixture corpus and expect exit status 1.** The status says that
  something failed, not which test or why.
- **Count the invalid test as a pass.** It weakens the gate for every
  test.

## Consequences

- The rule that UB in the set makes a test invalid is checked on the real
  tools in every run of the harness. If `fir-ref` stops listing the UB, or
  the harness stops judging it invalid, the run fails.
- No existing test changes. No sidecar had the key, and what counts as a
  pass for a test without it is the same.
- The key could mark a test invalid that should be fixed instead. It is
  for tests of this rule, such as #18's frozen divisor, and still fails a
  test whose set holds no UB.
