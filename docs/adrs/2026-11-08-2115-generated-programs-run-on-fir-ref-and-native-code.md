# Every pull request runs 500 generated programs on fir-ref and as native code

Status: accepted
Tier: direction; area: testing-and-harness

## Decision

- `generate::program` makes a program: a module of the backend's widths, and
  argument vectors for each function, often at boundary values. Its functions
  are random, bounded ones that iterate and then end, and ones planted to end in
  UB or out of fuel. Bounded functions mostly use ops that stay defined and feed
  what they return. Arguments hold no `poison`, since each one multiplies
  native runs.
- The first bounded function of each program, and half of the others, are
  built to stay defined, with 1,000,000 steps of fuel. UB, poison, a choice or
  a run out of fuel on one of their runs fails it: the generator is the second
  opinion, since UB allows native code anything.
- Each kind of UB is planted with a near miss, one operand away, whose result
  the generator states. A planted run must end as planted on `fir-ref`.
- Any other run is interpreter-only, and passes with no native run, when
  `fir-ref`'s set holds UB or a run out of fuel, or it chooses past 10 bits.
  Otherwise it is a differential test by the corpus's rules. A stuck path fails
  in every case. Runs have 20,000 steps of fuel, planted fuel runs 1,000.
- The `fir-random` hook runs seeds 0 to 499, the regression seeds and 500
  random texts for `fir-ref fmt`. In a run of 200 or more, at least half of the
  runs without an expected ending must reach native code, or it fails.

## Why

Every differential test came from hand-written texts, and M1 and M2 add much
backend code, where bugs appear. A first version that only limited the
generator to backend widths let a planted wrong `ashr` at `i16` pass 500
programs: out-of-range shifts gave poison, and most values never reached a
`ret`. Bounded, defined functions make a wrong result show as a wrong value.

## Rejected alternatives

- **Random functions alone.** Their values rarely reach a result, so a
  miscompile passes.
- **A second interpreter to catch a false UB in a random function.** The
  semantics lives only in Lean, so that is a direction call; until then such a
  run is interpreter-only.
- **Poison arguments in generated runs.** Each multiplies the native runs.
