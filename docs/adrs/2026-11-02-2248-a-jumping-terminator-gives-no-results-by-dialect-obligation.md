# In M0, a terminator that jumps gives no results by its dialect's obligation

Status: accepted

## Context

fir's generic spec lets a terminator have results, but its run never binds
them:

- `Func.OpValid`
  ([`lean/Fir/Validation/Rules.lean`](../../lean/Fir/Validation/Rules.lean))
  asks only that a terminator's results have the types that `returnTypes`
  gives.
- `Func.DominatesUse`
  ([`lean/Fir/Validation/Dominance.lean`](../../lean/Fir/Validation/Dominance.lean))
  puts a result of an op of block `a` in scope in every block that `a`
  strictly dominates.
- `DialectDenote.exit`
  ([`lean/Fir/Execution/Effects.lean`](../../lean/Fir/Execution/Effects.lean))
  returns an `Exit`, `goto i` or `ret`, which carries no values. On
  `goto i`, `Func.runOps`
  ([`lean/Fir/Execution/Interpreter.lean`](../../lean/Fir/Execution/Interpreter.lean))
  binds only the target block's arguments (`Func.jump`).

So in a dialect with a terminator that jumps and has results, a valid
function that uses one of those results in a block that the terminator's
block dominates gets stuck. For such a dialect, that breaks "a validated
module never gets stuck" (ADR-2026-10-29-2030). The core dialect is not
affected: `br` and `cond_br` have no results, and `ret` never jumps.

PR [#88](https://github.com/pmatos/funk/pull/88) made the condition a
hypothesis of the generic theorems, and
[#89](https://github.com/pmatos/funk/issues/89) asked whether the spec
should close the gap instead. The human ruled on 2026-11-02, on
[#89](https://github.com/pmatos/funk/issues/89#issuecomment-6590317336),
for option (c): keep it a dialect obligation in M0.

## Decision

- No spec definition changes. Validation has no rule that a terminator has
  no results, and `Exit` carries no values. `Func.OpValid`,
  `Func.InScope`, `DialectDenote.exit`, `Exit` and `Func.runOps` stay as
  they are.
- "A terminator that jumps gives no results" is a condition that each
  dialect meets for its own terminators. It is half of the `jumps` field
  of `Func.Local`
  ([`lean/Fir/Execution/Jumps.lean`](../../lean/Fir/Execution/Jumps.lean))
  and of `Func.InModule`
  ([`lean/Fir/Execution/Calls.lean`](../../lean/Fir/Execution/Calls.lean)):
  for each terminator `o` of the function, if `exit o.op args` may give
  `goto i`, then `i < succCount o.op` and `returnTypes o.op = []`.
- The generic theorems cover a function of a dialect only through these
  hypotheses. `Func.neverStuck_of_local` asks that the function be valid
  and run within itself (`Func.Local`): no op calls a function, a
  terminator that jumps meets the condition above, and a terminator that
  returns returns values of the function's result types.
  `Func.progress_of_local` also asks that every op be total (`OpTotal`).
  `Func.neverStuck_of_inModule` and `Func.progress_of_inModule` ask, of
  every function of the module, validity and `Func.InModule`, which has
  the same `jumps` and `returns` fields and allows calls to functions of
  the module; the second also asks that every terminator and every op
  with no callee be total. A function with a terminator that may jump and
  has results cannot meet these hypotheses, so the theorems say nothing
  of it.
- The core dialect meets the condition. `Core.Op.exit_goto`
  ([`lean/Fir/Core/CallFree.lean`](../../lean/Fir/Core/CallFree.lean))
  proves it of every core terminator; `Core.local_of_valid` uses it for
  every valid core function without a `call` op, and
  `Core.inModule_of_valid`
  ([`lean/Fir/Core/ValidRuns.lean`](../../lean/Fir/Core/ValidRuns.lean))
  for every function of a valid core module. So no path of a run of a
  function of a valid core module is stuck (`Core.neverStuck`).
- The choice between a validation rule (a) and values on `Exit` (b) is
  made when M3 designs exceptions and unwinding, which the roadmap's
  "Left out of v0" table gives to M3 (C++). That is the first place where
  a terminator with results would make sense.

This refines ADR-2026-10-29-2030. Its "a validated module never gets
stuck" holds for a dialect whose terminators meet the condition, and its
`Exit`, which "may grow (H6, unwinding)", does not grow in M0.

## Alternatives

- **(a) A generic validation rule:** a terminator has no results
  (`isTerminator op = true → returnTypes op = []`). It closes the gap for
  every dialect, but it forbids an `invoke`-style terminator, whose result
  is defined on one of its successors, which M3 may need.
- **(b) `Exit` carries values:** `exit` returns the terminator's results
  with the place to go, and the run binds them on the jump. It is the most
  general, but it changes `DialectDenote.exit` and the run, and likely the
  scope rule, since such a result may be defined on only some of the
  terminator's edges. Its shape depends on how M3 models unwinding.

## Consequences

- No fir program's meaning changes, and no proof changes.
- A dialect author who adds a terminator proves the condition for it, to
  have the progress and no-stuck theorems; validation does not check it.
  In a dialect that gives a jumping terminator results, a valid function
  that uses one of them in a block that the terminator's block dominates
  gets stuck.
- M3's design of exceptions and unwinding picks (a), (b) or another
  option, in an ADR that refines or supersedes this one.
