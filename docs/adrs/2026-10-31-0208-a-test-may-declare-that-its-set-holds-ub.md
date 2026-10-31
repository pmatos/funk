# A differential test may declare that its set holds UB, and then passes only when the harness judges it invalid for that reason

Status: accepted

## Context

ADR-2026-10-31-0003 makes a differential test invalid when UB is in its
set of outcomes. ADR-2026-10-30-2135 says that an invalid test never
counts as a pass, as [#13](https://github.com/pmatos/funk/issues/13)
puts it: "An invalid test is reported as a failure, never as a pass."
The run then exits with 1 (ADR-2026-10-30-2049). Until now only a unit
test on a hand-built set, with stand-ins for the tools, checked that
rule.

[#18](https://github.com/pmatos/funk/issues/18) asks for a real test of
it: "A differential test with a frozen divisor that can be zero is
reported invalid". #18 also asks that `pre-commit run --all-files`
passes. Put in the corpus as it is, that test fails every run of the
harness, so CI stays red. Kept out, it shows nothing. So #13's rule and
#18's two criteria cannot all hold literally for this test.

## Decision

- **The key.** A differential test may have `invalid = "ub"`: the test
  declares that it is invalid because its set holds UB. `"ub"` is its
  only value. It goes with neither `expect` nor `results`.
- **The run.** The harness runs the test as every differential test:
  `funk build` builds the module, exhaustive mode lists the set, native
  code runs, and ADR-2026-10-31-0003 judges it. Native code's result
  plays no part: UB in the set allows any result, a trap included.
- **The judgement.** The test passes when `funk build` built the module,
  exhaustive mode listed a set that holds UB, and that made the test
  invalid. A set that holds UB passes even when a path also runs out of
  fuel: the harness judges it invalid for the UB. Anything else fails
  it: a pass, a failure, invalid for fuel exhausted alone or for a budget
  exceeded, or a module that does not build.
- **The report.** The test's status is `passed`, and the summary and the
  exit status count it so. Its report line names the test with
  `(declared invalid)`, as `(interpreter only)` marks an interpreter-only
  test, and then says that the harness judges it invalid, with
  `fir-ref`'s reason. This is the one exception to #13's "never as a
  pass": the harness still judges the test invalid and says so, but the
  run counts that expected judgement as a pass.
- **Every other test** is judged as before. A test without the key that is
  invalid still fails the run.
- **The test.** `tests/fir/canonical/div-frozen.fir` holds #18's: `sdiv`
  at `i8` of 7 by `freeze` of a poison, which may choose 0, so the set
  holds `sdiv by zero`.
- `corpus.py` reads the key and `sets.declared_invalid` judges it.

## Alternatives

- **A harness test on a fixture, run with the real tools.** It keeps
  #13's wording literal. But the `fir-harness-test` hook runs the unit
  tests without building `fir-ref` or `funk`, so the test would need a
  second program that `scripts/check-harness.sh` runs, and a fixture
  corpus of its own, must-reject texts included, to load.
- **Run a fixture corpus and expect exit status 1.** The status says that
  something failed, not which test or why.
- **Count every invalid test as a pass.** It weakens the gate for every
  test: an invalid test that no one expected would pass unseen.

## Consequences

- The rule that UB in the set makes a test invalid is checked on the real
  tools in every run of the harness. If `fir-ref` stops listing the UB, or
  the harness stops judging it invalid, the run fails.
- No existing test changes. No sidecar had the key, and what counts as a
  pass for a test without it is the same.
- The key could mark a test invalid that should be fixed instead. It is
  for tests of this rule, such as #18's frozen divisor, and still fails a
  test whose set holds no UB.
