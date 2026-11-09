# Refinement asks monotonicity only of the ops a run can reach

Status: accepted
Tier: implementation; area: semantics

## Context

The refinement engine asked, as `hmono`, that every terminator and every
op with no callee be monotone at every op instance of the dialect, valid
or not. Since ADR-2026-11-02-1515, `LawfulDialectPoison` covers only
valid op instances. So a dialect that is lawful only on valid instances
could not get function-level refinement from the class alone
([#99](https://github.com/pmatos/funk/issues/99)). The core dialect met
`hmono` at every width with `Core.Op.monotone_all`, so nothing on main
was lost.

The human ruled on #99, in triage on 2026-11-05: do it now, as plain
Lean work before M1 adds memory. Pass module validity and in-module
membership through the refinement theorems, following
`Func.progress_of_lawful`, so that `hmono` is needed only at valid op
instances. The core theorems keep their statements.

## Decision

- The engine asks monotonicity only of the ops a run can reach: the ops
  of the source module's functions, and of the function that runs.
  `Func.OpsMonotone f` says that every terminator and every op with no
  callee of `f` is monotone. The guard of ADR-2026-11-02-1514 is
  unchanged; only what it ranges over is narrowed.
- `Func.runOps_allowed` and `Func.runOps_allowedBelow` carry the
  invariant that `f`'s ops are monotone and so are the ops `os` that
  they run. A jump goes to a block of the same function, and a call of
  the same function in both modules enters a function of the source
  module at its entry block. `CallsRefined.callee_allowed` and
  `CallsRefined.callee_allowedBelow` discharge that for the callee. A
  black-box call runs no op of the engine.
- `Func.runs_isRefinedBy_of_calls`, `Func.runs_args_isRefinedBy` and
  `Func.runs_replaceBody_isRefinedBy` take
  `hmono : ∀ g ∈ M.funcs, g.OpsMonotone` over the source module `M`, and
  the first two take `f.OpsMonotone` for the function that runs.
- Validity enters as for progress, in
  [`lean/Fir/Execution/Lawful.lean`](../../lean/Fir/Execution/Lawful.lean).
  `Func.Valid.opsMonotone` gives `f.OpsMonotone` for a valid `f` from
  monotonicity at valid op instances alone. With it, the class gives
  `Func.runs_args_isRefinedBy_of_lawful`, for every function of a module
  whose functions are valid, and `Func.runs_replaceBody_isRefinedBy_of_lawful`,
  for every valid module.
- `Core.args_isRefinedBy` and `Core.replaceBody_isRefinedBy` keep their
  statements. They take `Core.opsMonotone_all`: every core function's
  ops are monotone, valid or not.

This refines ADR-2026-11-02-1515, whose Consequences left this open.

## Alternatives

- **Ask `hmono` at valid op instances in the engine, with a valid
  module.** `Core.args_isRefinedBy` holds for every function of every
  core module, valid or not. It could not keep its statement.
- **Thread `Func.InModule`.** It is what progress needs. Refinement
  treats a stuck path as allowed, so it needs only that the ops are
  monotone. In-module membership here is `g ∈ M.funcs`.

## Consequences

- A lawful dialect gets both function-level refinement theorems for
  valid modules by the class alone. The test dialect `CoreProbe` is
  lawful and not monotone at `i0`, and gets them
  ([`lean/FirTest/LawfulRefine.lean`](../../lean/FirTest/LawfulRefine.lean)).
- Congruence in the callee needs nothing of the new body. #99 forecast
  that it would need a valid new body; it does not, because the engine
  never runs it: a call of `@g` is a black box, whose behaviour the
  hypothesis gives.
- A caller of `Func.runs_isRefinedBy_of_calls` or
  `Func.runs_args_isRefinedBy` passes one more hypothesis, `hf`, for the
  function that runs. `Func.runs_replaceBody_isRefinedBy` derives it from
  `hmono`, so its callers pass nothing new. Every theorem keeps its
  axioms: `propext`, `Classical.choice` and `Quot.sound` at most.
