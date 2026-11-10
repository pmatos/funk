# May produce poison means a poison result from operands with no poison, and the poison class sits beside it

Status: accepted
Tier: direction; area: semantics

## Context

ADR-2026-11-09-1541 gives each op a set of effects. One of them is "may
produce poison, which is the op's existing poison class", and
`DialectPoison` folds into the new class. The poison class
(ADR-2026-10-30-0818) is `propagates` or `exception`, and says how an op
treats poison operands. Read as one bit of the effect set, the class does
not fit the effect:

- `select` is an exception, yet it gives poison on a poison condition.
- `const` propagates, yet it never gives poison.
- `add` propagates, and gives poison on defined operands only with `nsw`
  or `nuw`.

Every effect must be proved sound when an op leaves it out
(ADR-2026-11-09-1541). "A result is never poison" holds only of `const` and
`freeze`, so it would tell a pass almost nothing. What a pass needs is
LLVM's `canCreatePoison`: whether poison can appear where no operand was
poison, as when an `add nsw` is hoisted past the check that kept it from
overflowing.

## Decision

- **The effect.** An op _may produce poison_ when, on some operands with no
  poison, a result may be poison. An op that leaves it out gives only
  defined results on defined operands, and the spec proves that
  (`MakesNoPoison` in `lean/Fir/Execution/EffectLaws.lean`).
- **The class beside it.** `DialectEffects`, in
  `lean/Fir/Execution/OpEffects.lean`, gives each op its poison class and
  its effect set. `DialectPoison` is gone. The class keeps its meaning and
  its obligations (`LawfulDialectPoison`); it now sits in the effect class,
  so an op's poison behaviour is declared in one place.
- **The core ops.** `poison`, the shifts, `add`, `sub` and `mul` with a
  flag, and `sdiv` and `udiv` with `exact` may produce poison. No other core
  op does.

## Alternatives

- **The effect is the class.** `propagates` would mean may produce poison,
  and `exception` would not. Under this ADR's obligation, no poison from
  operands with no poison (`MakesNoPoison`), that is sound. Of the
  exceptions, `select` gives poison only when an operand is poison, and
  `freeze` never does. The terminators give no results, and `call` has its
  callee's effects, so the obligation does not cover them. It would be
  unsound only if leaving the effect out meant "never returns poison". But
  it is imprecise: `const`, `icmp`, the bitwise ops, the width changes and
  `add`, `sub` and `mul` without flags would all be marked as producing
  poison, so an analysis that shows a value is not poison would learn
  nothing from them.
- **The effect means "a result may be poison".** Sound, but nearly every op
  has it, so passes could not use it.

## Consequences

- A pass reads both facts from one class: how poison flows through an op,
  and whether the op can create it.
- A new op declares both and proves each effect it leaves out, as
  ADR-2026-11-09-1541 asks.
