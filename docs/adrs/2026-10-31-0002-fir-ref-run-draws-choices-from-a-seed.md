# `fir-ref run --seed S` draws each choice from a generator seeded with S, and reports the values it drew

Status: accepted

## Context

A test that declares its results (ADR-2026-10-29-2017) is checked by
seeded runs of scripted mode: no sampled outcome may fall outside the
declared list, and none may be UB
([#14](https://github.com/pmatos/funk/issues/14)). Scripted mode
(ADR-2026-10-30-2218) needs the whole choice sequence up front, but which
choices a run makes, and their widths, are known only while it runs. Once
`cond_br` has rules (#16), which choices a path makes can depend on earlier
ones. The only place that names a choice's width today is a misfit's
message on standard error, and ADR-2026-10-30-2218 rejected a JSON kind for
a misfit.

## Decision

- **Sampled mode.** `fir-ref run --seed S` follows the path on which a
  generator, seeded with S, draws each choice as the run makes it. S is
  ASCII decimal digits, from 0 to 2^64 - 1. `--seed` does not go with
  `--choices` or `--exhaustive`.
- **Result.** ADR-2026-10-30-2218's scripted result, with one more field,
  `sequence`: the values drawn, in order, each spelled as a constant of
  its type, as `--choices` takes them. For example,
  `{"kind":"return","values":["0"],"choices":1,"sequence":["5"]}`. A path
  that reaches an op without rules is ADR-2026-10-30-1855's error.
- **Generator.** SplitMix64, seeded with S (`lean/FirRef/Sample.lean`). A
  choice of `w` bits takes one 64-bit draw. One draw in four gives a
  boundary bit pattern: 0, 1, all ones, the signed minimum or the signed
  maximum. Otherwise it takes ⌈w/64⌉ more draws and keeps their low `w`
  bits. A seed draws the same values on every machine.
- **Proofs.** The spec's `Core.sampled` walks the tree of choices with any
  generator. `Core.sampled_fits` proves that the values it chose are a
  sequence that fits the run, on which scripted mode reaches the same
  path; so `Core.sampled_outcomes` follows from `Core.scripted_outcomes`:
  a sampled outcome is a member of `(run n).outcomes`, whatever the
  generator. That the printed spelling reads back is tested, not proved.

## Alternatives

- **A machine-readable misfit that names the width.** The harness would
  rebuild a sequence one choice at a time, one run per choice, and read a
  second error format. It also reverses ADR-2026-10-30-2218.
- **A generator in the harness.** It cannot know the widths without that
  misfit.
- **A prefix from `--choices`, then draws.** Nothing needs it yet; #16 may
  add it when a branch must be pinned.
- **Lean's `StdGen`.** Its algorithm is the toolchain's to change; ours
  stays fixed across toolchain bumps.

## Consequences

- A sampled run is a scripted run that the harness can repeat, and its
  `sequence` can be pasted into a test as a witness.
- Changing the generator or the draw changes which values a seed draws.
  No corpus test depends on that, but `lean/FirTest/Sample.lean` pins a few
  draws.
