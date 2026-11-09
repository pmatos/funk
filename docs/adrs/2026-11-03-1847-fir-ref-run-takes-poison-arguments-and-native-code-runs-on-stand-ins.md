# `fir-ref run` takes `poison` as an argument, and native code runs a differential test on stand-ins in its place

Status: accepted
Tier: implementation; area: fir-ref

## Context

ADR-2026-10-30-1856 kept `poison` out of the arguments of `fir-ref run`,
as #10 worded them, and said that adding it needed the human's ruling.
[PR #61](https://github.com/pmatos/funk/pull/61) removed a `poison`
argument for that reason, and the corpus format spelled every argument
as a constant (ADR-2026-10-30-2050). The human ruled on 2026-11-03, by
dialog, that `fir-ref run` takes `poison` as an argument, as in
`fir-ref run f.fir @g 3 poison`, and that the harness uses it in
differential tests too ([#123](https://github.com/pmatos/funk/issues/123)).

The spec's runs already take poison: `Core.FuncRuns` holds a function's
run on every argument vector, poison included. Native code holds no
poison (ADR-2026-10-30-2248), and a built executable reads each argument
as a constant (ADR-2026-10-30-1233). The harness judges a differential
test by refinement on `fir-ref`'s set of outcomes (ADR-2026-10-30-2135,
ADR-2026-10-31-0003).

## Decision

- **The argument.** `fir-ref run` reads `poison` as an argument of any
  `iN`, spelled exactly so, as its output spells a poison value, and runs
  the function with poison there (`FirRef.readArg`). It is no argument of
  `ptr`, which has no values, and no choice: `--choices` takes constants
  only, since `freeze` chooses a value. Every other spelling is
  unchanged. The help text, `lean/Fir/Core/Text.lean` and
  `lean/Fir/Core/Modes.lean` say so.
- **Sidecars.** A test's `args` may hold `poison`. The harness passes it
  to `fir-ref` as it is: in an interpreter-only test, and in a
  differential test's exhaustive run, witnesses and seeded runs.
- **Stand-ins.** Native code runs on stand-ins in place of each poison
  argument of type `iN`: the boundary bit patterns that sampled mode
  favours (ADR-2026-10-31-0002), 0, 1, all ones, the signed minimum and
  the signed maximum, each once, so `false` and `true` at `i1`. It runs
  once on each combination: up to `5 ** k` runs for `k` poison
  arguments, fewer where the patterns coincide, as at `i1` and `i2`
  (`scripts/harness/standins.py`).
- **Judgement.** Each native result is judged against `fir-ref`'s
  outcomes on the poison, by the rules of ADR-2026-10-30-2135 and
  ADR-2026-10-31-0003, unchanged. The test passes when every result
  passes, and the report names the first vector that does not. UB among
  `fir-ref`'s outcomes still makes the test invalid.
- **Past the choice budget.** When a vector's result fails a test whose
  run on the poison chooses more than the budget, the harness also runs
  `fir-ref` on that vector: exhaustively, or on each seed when that run
  too is past the budget. UB there makes the test invalid. So does a
  path out of fuel there, as it does in a set: the result depends on the
  budget. Otherwise the failure stands, and the report shows `fir-ref`'s
  outcome on the vector.

## Why it is sound

Correct native code passes every such test, calls included:

1. A run with a value in place of poison refines the run with poison.
   `Core.args_isRefinedBy` (`lean/Fir/Core/CallRefine.lean`) proves it
   for every function of every core module, calls and recursion
   included: on arguments that refine others, a poison by any value, the
   function's observable behaviour refines its behaviour on those others.
   It is `Func.runs_args_isRefinedBy` with `Core.Op.monotone_all`.
2. Native code refines `fir-ref` on defined values. This is S4's
   correctness of the backend (ADR-2026-10-29-2008), which differential
   tests check; it is not a theorem.

By transitivity (`Core.behaviour_isRefinedBy_trans`), a correct native
result on stand-ins refines the behaviour on the poison. At the test's
budget, where no path runs out of fuel, that behaviour is the run's set
of outcomes (`observable_eq_at`, `Func.fuelMonotone`), which exhaustive
mode lists (`Core.exhaustive_outcomes`). So, within the choice budget,
a failure is a bug of native code on the vector it names. UB in a
refining run needs UB in the run it refines, so a test whose poison run
has no UB never runs native code on a vector that is UB, such as a zero
divisor.

Past the choice budget, the test's declared results stand for that set:
scripted and sampled mode give only its outcomes
(`Core.scripted_outcomes`, `Core.sampled_outcomes`), and seeded runs
only sample it, as ADR-2026-10-31-0003 says. They may miss UB that a
stand-in reaches, such as the signed minimum divided by -1. Hence the
run of `fir-ref` on a failing vector. UB in the run on the vector needs
UB in the behaviour on the poison (`Core.args_isRefinedBy`), which at
the test's budget is UB or a path out of fuel (`Func.fuelMonotone`):
either makes the test invalid. No theorem puts a path out of fuel in
the run on the poison at the same budget when the vector's run has one;
the test is invalid then by the rule for a set, since only a larger
budget decides it. Any other failure past the budget is a bug of native
code on the vector, or a set of declared results that misses an
outcome; `fir-ref`'s outcome on the vector tells which.

The test is weaker than one on the stand-ins' own values: where the
poison reaches a result, any value passes. Where it does not, native
code must give the defined value on every stand-in.

## Alternatives

- **Also run `fir-ref` on each vector, and compare exactly.** The ruling
  compares with the run on the poison; tests of defined values exist.
  The harness runs `fir-ref` on a vector only past the budget, after a
  failure, to find UB or a path out of fuel, not to judge the result.
- **One stand-in, such as 0, which `poison` lowers to
  (ADR-2026-11-03-1616).** Bugs gather at the boundary bit patterns.
- **The same stand-in for every poison argument.** Five runs whatever
  `k`, but no two poison arguments ever differ.
- **Random stand-ins.** A failure would not reproduce.

## Consequences

- A differential test with `k` poison arguments costs one `fir-ref` run,
  as before, and up to `5 ** k` native runs. The corpus's tests pass at
  most two. Past the budget, a failing vector costs one more `fir-ref`
  run, or one per seed.
- `tests/fir/canonical/poison-arg-iN` passes poison to functions of each
  kind at the eight widths of the coverage matrix. The matrix counts what
  a test runs, so its rules do not change.
- `funk build`'s executables still take constants only.
