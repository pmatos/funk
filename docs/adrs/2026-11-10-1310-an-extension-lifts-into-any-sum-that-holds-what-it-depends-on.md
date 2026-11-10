# An extension lifts into any sum that holds what it depends on, through an inclusion of types

Status: accepted
Tier: direction; area: semantics

## Context

In the spec's sum `base ⊞ e` (ADR-2026-11-09-2306), the extension `e`
states its classes for `base.over e`: it is written over the whole base
before it. ADR-2026-11-09-1543 says that a dialect declares the dialects it
depends on. So two extensions written over the core, such as a GPU dialect
and a test dialect, could not both be added to one module: the second would
need classes over the sum of the core and the first, which it does not
know. Stage 2 of [#227](https://github.com/pmatos/funk/issues/227) lifts an
extension into such a sum.

## Decision

- **An inclusion of types.** `TyIncl A B` (`lean/Fir/Sum/Inclusion.lean`)
  says that the types `A` are among the types `B`: a map `incl` of types,
  its projection `proj`, and maps `up` and `down` of values that undo each
  other. The base of a sum is included by `TyIncl.inl`. `TyIncl.over`
  includes the types of an extension over a base in those of the same
  extension over a larger base, and `TyIncl.comp` composes two inclusions.
  So a dialect held anywhere in a nested sum is included in the sum's types.
  An inclusion is lawful when crossing it keeps poison and refinement.
- **The lift.** `e.lift dep ι` (`lean/Fir/Sum/Lift.lean`) is `e`, written
  over `dep`, lifted by an inclusion `ι` of `dep`'s types in a larger base
  `big`. Its classes over `big` come from `e`'s over `dep` and from `big`'s:
  `e`'s signature with `dep`'s types included, `e`'s text and rules for its
  ops and own types, `big`'s for `big`'s types, and `e`'s semantics on values
  moved across the inclusion. `big ⊞ e.lift dep ι` is then an ordinary sum.
- **What a lifted op sees.** An op of `e` sees the symbols whose types are
  all `dep`'s or its own, and is valid only where the function's result types
  all are. This is ADR-2026-11-09-2353 with `e` in place of the base, within
  the human's ruling on it.
- **Laws.** The lift of an extension with lawful text has lawful text when
  `big`'s set is lawful and `e`'s name is new to `big`, and it names only
  dialects of `big`'s set when `dep`'s set is in `big`'s. The lift of a lawful
  extension is lawful when the inclusion is lawful and `e` accepts each type
  of `dep` whose inclusion `big` accepts. The round trip, well-formedness
  and the poison obligations hold for `big ⊞ e.lift dep ι` with no new
  assumption.
- **Tests.** A sum of three dialects, the core, the toy dialect `toy` and
  the bit dialect `bit`, each extension written over the core alone, is
  lawful by these theorems (`lean/FirTest/Deps.lean`). The bit dialect is
  the first test dialect with a name other than `toy`, since two dialects
  of one name cannot share a sum.

This refines ADR-2026-11-09-2306 and ADR-2026-11-09-2353.

## Alternatives

- **A class saying which base an extension depends on.** Instance search
  could then lift an extension by itself. But the class would need to find
  `dep` from `big` alone, and would give a second instance beside `e`'s own
  over `dep`. The lift names `dep` and the inclusion, so search finds them.
- **A type equation in place of maps of values.** `⟦incl t⟧ = ⟦t⟧` would
  move values by casts, which every proof about poison would have to undo.
  For the base of a sum, `up` and `down` are the identity.

## Consequences

- An extension is written once, over the dialects it depends on, and joins
  any sum that holds them.
- The limits of ADR-2026-11-09-2306 and ADR-2026-11-09-2353 stay: core ops
  carry core types only, and an op that cannot write a function's result
  types is invalid in it.
- A lifted op sees less than the same extension written over the whole
  larger base would: in a function that returns a type of a dialect `e`
  does not depend on, no op of `e` is valid. Relaxing this is relaxing
  ADR-2026-11-09-2353, for base ops and lifted ops together.
- A module does not yet declare its dialect set in the text. Stage 4 of #227
  adds the declaration and the check on both sides.
