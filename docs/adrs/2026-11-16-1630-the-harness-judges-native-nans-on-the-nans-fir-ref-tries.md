# The harness judges a native NaN on the part of the set that fir-ref lists when it tries native code's NaNs

Status: accepted
Tier: direction; area: testing-and-harness

## Decision

- **First run.** A differential test runs `fir-ref run --exhaustive
  --nans` with no NaN given: at a NaN choice it tries the positive quiet
  NaN, at no cost to the budget (ADR-2026-11-16-0855). A run with no NaN
  choice is `complete` and judged as before (ADR-2026-10-30-2135).
- **A part of the set.** Otherwise each outcome listed is one of the set,
  so a stuck one fails the test, UB or fuel exhausted makes it invalid,
  and a native result that refines one passes.
- **Native code's NaNs.** When the native result refines none, and holds
  NaNs, the harness runs `fir-ref` again with their bits as `--nans` and
  judges on that list. A NaN is a float result that is a NaN, or an integer
  result whose bits are a NaN of a float format of its width, as a NaN
  that went through `bitcast` or memory is. No other values are given.
- **Past the budget.** Each NaN given costs bits at every NaN choice, so
  with one given, 17 NaN choices on a path pass the 16-bit budget. That
  run proves nothing, and the test is invalid unless it declares its
  results.
- **A failure says why.** A result outside the list fails, and the
  failure says that the NaN choices were cut short.
- **Declared results.** A test that computes on a NaN's bits declares its
  results, each with a witness. Against a part of the set, each listed
  outcome must be declared, 32 seeded runs must each give a declared
  result, and native code must refine one.

The human ruled the subset and the declared fallback on 2026-11-16 (#219
Q1), and that NaN tries count against the 16-bit budget (#219 Q2).

## Why

A listed outcome is a proof that it is in the set
(`Gpu.exhaustiveNaN_memOutcomes`), so a pass is sound. Native code's own
NaNs are the few that matter, and trying them only after a miss keeps the
values few and every run without a NaN choice as it was.

## Rejected alternatives

- **Native code first, its NaNs always given.** It charges the budget on
  runs that pass with the quiet NaN, and runs native code before a
  reference verdict that decides the test.
- **Any native NaN where fir-ref lists a NaN.** It holds only while no op
  reads a NaN's bits, and `bitcast` and memory read them.
- **The bits of every result.** Each value costs bits at every NaN choice.
