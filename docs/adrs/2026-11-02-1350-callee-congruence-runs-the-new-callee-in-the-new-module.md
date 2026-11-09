# Congruence in the callee compares the new callee in the new module with the old in the old

Status: accepted
Tier: implementation; area: semantics

## Context

[#20](https://github.com/pmatos/funk/issues/20) asks for congruence in
the callee: replacing a callee with a function that refines it
(`FuncRuns.IsRefinedBy`, over `Core.FuncRuns`) refines every caller,
recursion included. The statement has to fix what replacing a callee is,
and in which module the new callee's runs are taken.

Facts that constrain it:

- A caller reaches a callee only by its symbol (ADR-2026-10-29-2012).
- `FuncRuns.IsRefinedBy` compares two `FuncRuns` of one argument type.
- A callee may call back into its module, itself included, so its runs
  depend on the module they run in.

## Decision

With `M'` for `M.replaceBody g.name b`, the hypothesis is
`funcRuns M g ⊑ funcRuns M' (g.replaceBody g.name b)`: the new `@g`, run
in the new module, refines the old `@g`, run in the old. The conclusion
is the same relation for every function `f` of `M`:
`funcRuns M f ⊑ funcRuns M' (f.replaceBody g.name b)`, which is `f`
itself when `f` is not `@g` (`Core.caller_isRefinedBy`). The core
theorem, `Core.replaceBody_isRefinedBy`, asks only that `M` be valid,
for its unique symbols.

Replacing a callee is replacing a body. `M.replaceBody s b` is the module
`M` with the region `b` in place of the body of its function `@s`. Every
function keeps its symbol, its parameters and its result types. The new
function has the old one's parameters, so the runs of both are
`FuncRuns` of one type, and the statement needs no cast.

## Alternatives

- **The new callee run in the old module.** False: if `@g` returns `0`,
  the body `call @g` refines it in the old module, where it calls the old
  `@g`, but in the new module it calls itself and never returns.
- **A new function with parameters of its own names.** Its `FuncRuns`
  has another type, so the hypothesis and every caller's conclusion would
  need a cast.

## Consequences

- A rewrite that replaces a function's body is correct for every caller
  once the function, run in the new module, refines itself in the old.
  When the new body calls back into the module, proving that may need
  its own induction.
- The comparison is between real behaviours when the new function is
  valid in the old module's context (`Module.valid_replaceBody`). A body
  that gets stuck at once meets the hypothesis with an empty behaviour,
  which refines every source.
