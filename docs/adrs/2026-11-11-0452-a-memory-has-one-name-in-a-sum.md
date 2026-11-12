# A memory has one name in a sum: an extension's memories are its base's and its own, and a lift maps them

Status: accepted
Tier: direction; area: semantics

## Context

In the spec's sum `base ⊞ e` (ADR-2026-11-09-2306), the memories were each
side's, kept apart: `Mem base ⊕ Mem (base.over e)`. An extension that names
a memory of its base, such as a GPU dialect that loads from the core's
default memory, would name it a second time. The sum would then see two
memories, so a pass could reorder the core's store with the extension's
load of the same memory. A lift (ADR-2026-11-10-1310) had the same problem
for `dep`'s memories in `big`.

## Decision

- **An extension's memories are its base's and its own.**
  `DialectMemOver base e`
  ([`Sum/Dialect.lean`](../../lean/Fir/Sum/Dialect.lean)) splits each memory
  name of `e` over the base into one of the base's or one of `e`'s own
  (`Own`), and back. `ofBase` is the name that `e` gives a base memory.
  This mirrors types: `base.over e` has `base.Ty ⊕ e.Ty`.
- **The sum names memories as the extension does.** `Mem (base ⊞ e)` is
  `Mem (base.over e)`. A base op's effects are renamed by `ofBase`.
- **A lift carries a memory map.** `e.lift dep ι μ` records
  `μ : Mem dep → Mem big` beside the type inclusion `ι`. The lift's
  memories are `Mem big ⊕ Own`. `liftMem μ` sends `e`'s name for a memory
  of `dep` to `μ` of it, and keeps `e`'s own names
  ([`Sum/Lift.lean`](../../lean/Fir/Sum/Lift.lean)). So `big ⊞ e.lift dep ι μ`
  names each memory of `dep` once (`liftMem_ofBase`).
- **Memory maps compose as inclusions do.** `ofBase` maps the base of a
  sum. Composition reaches a base held deeper in a nested sum, and the
  lift's `liftMem` maps the memories of an extension over a smaller base
  into the larger one. `lean/FirTest/Deps.lean` builds each.

This refines ADR-2026-11-09-2306 and ADR-2026-11-10-1310.

## Alternatives

- **One global type of memory names, such as `ptr<N>`'s `N`.** Sums would
  need no map. But each dialect names its own memories
  (ADR-2026-11-09-1541), and two dialects could then claim one name.
- **Find the memory map by instance search.** ADR-2026-11-10-1310 records
  the type inclusion on the lift rather than searching for it. The memory
  map is recorded beside it, for the same reason.

## Consequences

- Every extension that declares effects gives a `DialectMemOver` instance.
  The test dialects have no memory of their own: their memories are
  `Mem core ⊕ Empty`.
- The type of a lift mentions `μ`, so every lift names its memory map, even
  one whose extension declares no effects.
- `μ` is the caller's choice, as `ι` is, and nothing checks that it names
  each memory of `dep` as `big` does. The right map for a base held in a
  sum is `ofBase`, composed through each level of the sum, as `Deps.lean`
  builds it.
- The Rust registry names memories by strings. It does not mirror this
  yet, since no registered dialect has a memory (ADR-2026-10-30-1146).
