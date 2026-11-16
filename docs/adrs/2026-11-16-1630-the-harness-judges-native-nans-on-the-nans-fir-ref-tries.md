# The harness judges a native NaN on the part of the set that fir-ref lists when it tries native code's NaNs

Status: accepted
Tier: direction; area: testing-and-harness

## Decision

- **First run.** A differential test runs `fir-ref run --exhaustive
  --nans` with no NaN given, so a NaN choice tries the positive quiet NaN
  at no cost to the budget (ADR-2026-11-16-0855). A `complete` run is
  judged as before (ADR-2026-10-30-2135).
- **A part of the set.** Otherwise the set's rules apply to the outcomes
  listed, and a native result that refines one passes.
- **Native code's NaNs.** When the native result refines none, the
  harness runs `fir-ref` again with native code's NaN results as `--nans`:
  each float result that is a NaN, and each integer result whose bits are
  a NaN of a float format of its width. No other values are given.
- **Past the budget.** With one NaN given, 17 NaN choices on a path pass
  the 16-bit budget. That run proves nothing, and the test is invalid
  unless it declares its results.
- **Declared results.** A test that computes on a NaN's bits declares its
  results, each with a witness. Each listed outcome must be declared, and
  the seeded runs and native code must give declared results.

A result outside the list fails, saying that the NaN choices were cut
short. The human ruled the subset and the declared fallback (#219 Q1) and
that NaN tries count against the budget (#219 Q2) on 2026-11-16.

## Why

A listed outcome is proved to be in the set
(`Gpu.exhaustiveNaN_memOutcomes`), so a pass is sound. Native code's own
NaNs are the few that matter, and trying them only after a miss keeps
every run without a NaN choice as it was.

## Rejected alternatives

- **Native code's NaNs always given.** It charges the budget on runs that
  pass with the quiet NaN.
- **Any native NaN where fir-ref lists a NaN.** It holds only while no op
  reads a NaN's bits, and `bitcast` and memory read them.
- **The bits of every result.** Each value costs bits at every NaN choice.
