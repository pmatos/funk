# Congruence in the callee replaces a body, and runs the new callee in the new module

Status: accepted

## Context

[#20](https://github.com/pmatos/funk/issues/20) asks for congruence in
the callee: replacing a callee with a function that refines it
(`FuncRuns.IsRefinedBy`, over `Core.FuncRuns`) refines every caller,
recursion included. The statement has to fix what replacing a callee is,
in which module the new callee's runs are taken, and what the proof may
assume of a dialect.

Facts that constrain it:

- A caller reaches a callee only by its symbol (ADR-2026-10-29-2012).
- `FuncRuns.IsRefinedBy` compares two `FuncRuns` of one argument type.
- A callee may call back into its module, itself included, so its runs
  depend on the module they run in.
- A behaviour says nothing of steps, while a caller goes on with the
  steps that its callee leaves (ADR-2026-11-02-0836).
- Divergence is running out of fuel at every budget, which assumes
  finitely many ways to go at each step
  ([`lean/Fir/Execution/Behaviour.lean`](../../lean/Fir/Execution/Behaviour.lean)).

## Decision

- **Replacing a callee replaces a body.** `M.replaceBody s b` is the
  module `M` with the region `b` in place of the body of its function
  `@s`. Every function keeps its symbol, its parameters and its result
  types. The new function has the old one's parameters, so the runs of
  both are `FuncRuns` of one type, and the statement needs no cast.
- **The new callee runs in the new module.** With `M'` for
  `M.replaceBody g.name b`, the hypothesis is
  `funcRuns M g ⊑ funcRuns M' (g.replaceBody g.name b)`, and the
  conclusion is the same relation for every function `f` of `M`:
  `funcRuns M f ⊑ funcRuns M' (f.replaceBody g.name b)`, which is `f`
  itself when `f` is not `@g` (`Core.caller_isRefinedBy`). The core
  theorem, `Core.replaceBody_isRefinedBy`, asks only that `M` be valid,
  for its unique symbols.
- **The general theorem asks for finitely many argument vectors.**
  `Func.runs_replaceBody_isRefinedBy` asks that every op be monotone, that
  the refinement of values be reflexive and transitive, and that `@g`'s
  parameter types have finitely many argument vectors. Then one budget
  bounds every run of the new `@g` that does not diverge, which the proof
  of divergence needs. Every core type has finitely many values.

## Alternatives

- **The new callee run in the old module.** False: if `@g` returns `0`,
  the body `call @g` refines it in the old module, where it calls the old
  `@g`, but in the new module it calls itself and never returns.
- **A new function with parameters of its own names.** Its `FuncRuns`
  has another type, so the hypothesis and every caller's conclusion would
  need a cast.
- **König's lemma over the tree of choices** in place of finitely many
  arguments. It covers every dialect whose choices are finite, but needs
  an infinite path through `ChoiceTree` runs at every budget, which the
  spec does not have. M0's types do not need it.

## Consequences

- A rewrite that replaces a function's body is correct for every caller
  once the function, run in the new module, refines itself in the old.
  When the new body calls back into the module, proving that may need
  its own induction.
- A dialect with a type of infinitely many values, such as memory (S3),
  cannot use the general theorem as it is. It needs König's lemma or an
  argument of its own.
- Refined arguments, #20's other theorem, need no finiteness: they
  replace no callee.
