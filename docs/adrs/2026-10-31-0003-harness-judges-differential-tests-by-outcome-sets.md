# The harness judges a differential test by its set of outcomes, and checks declared results by their witnesses and by seeded runs

Status: accepted

## Context

ADR-2026-10-29-2017 makes a run's behaviour a set of outcomes once
`freeze` of poison chooses a value, and gives the harness its rule: a
native result passes if it is in the set; a run with no choice is compared
exactly; a test is invalid when its set holds UB, or when its choices
exceed the budget and it declares no results. A declared result comes with
a witness that scripted mode checks, and seeded runs check that no sampled
outcome falls outside the list (#14). ADR-2026-10-30-2135 judges a test
on one outcome, and ADR-2026-10-30-2050's format has no place for
declared results or for the path of an interpreter-only test.
`fir-ref run` has exhaustive, scripted and sampled modes
(ADR-2026-10-30-2218, ADR-2026-10-31-0002).

## Decision

- **Every differential test runs in exhaustive mode**, at its fuel budget
  and the default choice budget of 16 bits.
  - A run that makes no choice has one outcome, judged exactly as
    ADR-2026-10-30-2135 says: refinement, with poison refined by any value.
  - Otherwise UB anywhere in the set makes the test invalid, fuel exhausted
    on any path makes it invalid, and a stuck path fails it. Native code
    passes when its result refines one outcome of the set.
  - Past the budget, a test that declares no results is invalid.
- **Declared results.** A differential test may have `results`, a list of
  `{ values = [...], witness = [...] }`: the values, `poison` included,
  and the choices on which `fir-ref` gives them, as `--choices` takes
  them. No two have the same values.
  - Each witness runs with `--choices`, and must give exactly its values.
    A witness that no longer fits is `fir-ref`'s error, which fails the
    test; one that reaches UB or fuel exhausted makes it invalid.
  - Within the budget, the set must be exactly the declared results: a
    declaration that misses an outcome fails.
  - Past the budget, `fir-ref run --seed S` runs for each S from 0 to 31.
    Each must give a declared result; UB or fuel exhausted makes the test
    invalid. The failure names the seed and the values it drew.
  - Native code passes when its result refines one declared result.
- **Interpreter-only tests** may name their path with `choices`, which the
  harness gives to `--choices`. Without it, the sequence is empty, so a
  run that chooses fails loudly.

## Alternatives

- **Sample on every declared test.** Within the budget, the set is exact,
  so samples add nothing.
- **A per-test choice budget.** The budget bounds the harness's cost; a
  test past it declares its results instead.
- **Fail rather than invalidate a sampled UB.** A sampled outcome is a
  member of the set (`Core.sampled_outcomes`), and UB in the set makes a
  test invalid.

## Consequences

- Each differential test costs one exhaustive run; a declared test past
  the budget costs one more run per witness and 32 sampled runs.
- Seeded runs only sample: a declaration can still miss a result that no
  seed draws. Boundary bit patterns come up in one draw in four
  (ADR-2026-10-31-0002), so the likeliest misses are drawn.
- #18 adds the corpus test whose set holds UB, a frozen divisor that can
  be zero; until then a unit test on a hand-built set covers that rule.
