# Every pull request runs 500 generated programs on fir-ref and as native code

Status: accepted
Tier: direction; area: testing-and-harness

## Context

All differential tests came from hand-written texts (#165). The module
generator only served validation: its widths are mostly ones that the
backend cannot lower, and nothing ran its modules. M1 and M2 will add much
backend code, where bugs appear.

A first version only limited the generator to backend widths. Nearly every
run that returned did so within 30 steps, and a planted wrong `ashr` at
`i16` passed 500 programs: shift amounts were almost always out of range,
which gives poison, and most values never reached a `ret`.

## Decision

- `generate::program` makes a program: a module of the backend's widths, and
  argument vectors for each function, often at boundary values. Its
  functions are random ones, bounded ones that iterate and then end
  (`bounded.rs`), and ones planted to end in UB or out of fuel.
- Bounded functions mostly use ops that stay defined and feed what they
  return, so that a wrong result shows as a wrong value.
- The first bounded function of each program, and half of the others, are
  built to stay defined: no op that makes poison or UB on defined operands,
  calls only of functions like themselves, and 1,000,000 steps of fuel, more
  than they can take. If `fir-ref` reports UB, poison, a choice or a run out
  of fuel on one of their runs, the run fails. The generator is the second
  opinion, since UB allows native code anything.
- Each kind of UB is planted with a near miss, one operand away, whose result
  the generator states: a division by zero or by poison, the signed minimum
  by -1, poison by -1, and `cond_br` on poison.
- A run's arguments hold no `poison`, since each one multiplies native runs.
  Poison comes from ops.
- `scripts/check-random-programs.sh`, the `fir-random` hook, runs seeds 0 to
  499, the regression seeds and 500 random texts for `fir-ref fmt`. With its
  tools already built, the hook took 39 seconds locally.
- A planted run must end as planted on `fir-ref`.
- Any other run is judged by `differential.evaluate_generated`. It is
  interpreter-only, and passes with no native run, when `fir-ref`'s set holds
  UB or a run out of fuel, or when the run chooses past 10 bits. A generated
  run cannot declare its results, and nothing else can judge these runs.
  Otherwise it is a differential test by the corpus's rules, and a stuck
  path fails in every case.
- Runs have 20,000 steps of fuel, and planted fuel runs 1,000.
- At least half of the runs without an expected ending must reach native
  code, in a run of 200 or more, or the hook fails. A change to the generator
  cannot leave the check empty.

## Consequences

- A false UB in a purely random function goes unnoticed: such a run is
  interpreter-only, and only the proof of `fir-ref`'s machine and the
  corpus's hand-written tests stand behind it. A second interpreter would
  cover it, but the semantics lives only in Lean, so that is a direction
  call.
- Bounded recursion is at most 15 deep per function. Random functions recurse
  until they return or fuel stops them, so a run that returns very deep could
  overflow the native stack and fail although the code is right. A run of
  10,000 fresh programs, 83,053 of its runs compared with native code, showed
  none. If one appears, it is this limit, not a miscompile.
- A change to the generator changes which program each seed means.
