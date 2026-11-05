# `decide` on validity runs `fir-ref`'s check through instances of high priority

Status: accepted

## Context

ADR-2026-10-30-1742 makes `fir-ref`'s calls of `Module.problems` and
`Func.problems` run copies compiled after the `@[csimp]` theorem that
replaces the spec's walk of nested blocks, so the check takes no stack per
level of regions. ADR-2026-11-03-1715 replaces dominance in the same copies.

It left `decide` out. The spec's instances `Decidable m.Valid` and
`Decidable (f.Valid ctx)`, in
[`CheckModule.lean`](../../lean/Fir/Validation/CheckModule.lean), are
compiled in the spec, before any theorem of `lean/FirRef/`. The compiler
inlines an instance at each use as its own module compiled it, so
`decide m.Valid` ran the spec's `Module.problems` and its walk, even in code
compiled after `FirRef.Fast`, and aborted with a stack overflow on regions
nested 1,000,000 deep. A `@[csimp]` theorem on an instance does not help:
the instance is inlined before the theorem applies. So ADR-2026-10-30-1742
ruled that `fir-ref` decides validity with `Module.problems`, never with
`decide`, until [#47](https://github.com/pmatos/funk/issues/47) fixed it.

## Decision

- **Two instances of priority `high` in
  [`lean/FirRef/Validate.lean`](../../lean/FirRef/Validate.lean), after
  `problems_eq_moduleProblems`:** `FirRef.decidableValid` for
  `Decidable m.Valid` and `FirRef.decidableFuncValid` for
  `Decidable (f.Valid ctx)`. Each is the spec's instance word for word, so
  `decidableValid_eq` and `decidableFuncValid_eq` prove them equal to the
  spec's by `rfl`. Those theorems rest on Lean's standard axioms only, as
  `Module.problems_eq_nil_iff` does, which both instances use. Compiled
  after the theorems, their code calls `FirRef.moduleProblems` and
  `FirRef.funcProblems`.
- **Where they apply.** `FirRef.Fast` imports `FirRef.Validate`, so every
  module compiled after it, `FirRef.Main` and `FirTest` included, resolves
  `decide m.Valid`, `if m.Valid then …` and `decide (f.Valid ctx)` to them,
  and runs `fir-ref`'s check at any depth. In a module that does not import
  `FirRef.Fast`, `decide` still runs the spec's walk, as every call of a
  replaced spec function does there (ADR-2026-10-30-1450).
- **The rule of ADR-2026-10-30-1742 changes.** `fir-ref` may decide
  validity with `decide`, in a module that imports `FirRef.Fast`.
  `fir-ref validate` still calls `Module.problems`, because it reports each
  problem, not only the verdict.
- **Tests.** [`lean/FirTest/Validate.lean`](../../lean/FirTest/Validate.lean)
  pins the instances that `#synth` finds, and runs `decide` on a module
  nested 1,000,000 levels deep, which is not valid; without the
  instances, its build aborts with a stack overflow. No valid module nests
  regions in M0, since every op that owns one is rejected, so the valid
  case is a module of 1,000,000 ops in one block.

## Alternatives

- **A `@[csimp]` theorem on the spec's instance.** The compiler inlines the
  instance first, so the theorem never applies.
- **Compile the spec's instances after the theorems.** The spec's modules
  cannot import `lean/FirRef/`, which imports them, and the spec does not
  change for `fir-ref` (ADR-2026-10-30-1450).
- **Keep the rule "never `decide`".** It is a trap: a later `if m.Valid`
  in `fir-ref` would take stack per level, and no test would catch it.

## Consequences

- `decide` on validity gives the spec's answer, proved, and takes no stack
  per level of regions wherever `FirRef.Fast` is imported.
- A proof by `decide` unfolds the same definition as with the spec's
  instance: the two are equal by `rfl`.
- A change to either spec instance breaks `rfl` in its theorem, and so the
  build, until the copy follows it.
