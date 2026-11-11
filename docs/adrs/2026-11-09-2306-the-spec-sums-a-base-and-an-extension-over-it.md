# The spec sums a base dialect and an extension over it, routing ops and types by prefix

Status: accepted; refined by ADR-2026-11-10-1306, ADR-2026-11-10-1310 and ADR-2026-11-11-0452
Tier: direction; area: semantics

## Context

ADR-2026-11-09-1543 decides that a module's dialects combine as a sum,
routed by the `name.` prefix, for ops, types and attributes. It also moves
the sum from `lean/FirTest/` into the spec, and lets a dialect name the types
of the dialects it depends on.
[#227](https://github.com/pmatos/funk/issues/227) builds this. Its first
stage puts the sum in the spec.

The test sum of ADR-2026-10-30-2040 shares one type set between its two
sides, so an extension cannot add types. A plain sum of two dialects, with
types `Ty₁ ⊕ Ty₂`, would not let an extension's op take a core value. The
core's `i8` would then also have two spellings. ADR-2026-11-09-2257 keeps
`DialectView` as the way each side of a sum sees a function, with
`DialectView.ty` projecting the summed types.

## Decision

- **An extension over a base.** An extension `e` has ops `e.Op` and its own
  types `e.Ty`. It states each class of a dialect for `base.over e`, whose
  types are `base.Ty ⊕ e.Ty`, so its ops can take the base's types. The base
  is what `e` depends on. A dialect with no types of its own takes `Empty`.
- **The sum.** `base ⊞ e` (`lean/Fir/Sum/Dialect.lean`) has the ops
  `base.Op ⊕ e.Op` and the types `base.Ty ⊕ e.Ty`. Each class is lifted to
  it, side by side: signature, text, validation (decidable), poison classes,
  semantics and calls, and the meaning, poison and refinement of the summed
  types. A base op takes and gives the base's values as the sum's `.inl`
  values. Each side's function rule sees the function through its own view.
  Any number of dialects is a nested sum, `core ⊞ a ⊞ b`.
- **Routing by prefix.** A word belongs to the dialect named before its
  first `.`, and a bare word to the core (`wordDialect`). Reading an op or a
  type sends a word of `e`'s name to `e`, and every other word to the base. A
  type is routed by its head word.
- **Attributes.** An op's attributes go with the op, to the side that its
  name picks. They are generic terms, read by the op's own dialect, so the
  sum does not route them on their own. The dialect-set laws below say
  which dialects their words may name.
- **What the base sees** of an op's context is ADR-2026-11-09-2353.
- **Dialect sets.** `DialectSet d` lists the dialects whose names the words
  of `d` may use. The core's set is empty, and the set of `base ⊞ e` is the
  base's set and `e`'s name. `LawfulDialectSet` says that every op name,
  every word of an op's attributes and every word of a valid type names a
  dialect of the set. `LawfulDialectName base e` says that `e` writes its
  own ops and types under its name.
- **Laws.** The sum's text is lawful exactly when every word goes to its
  own side (`Dialect.sum.lawful_iff`). That holds when the base's set is
  lawful, `e` names its words, and `e`'s name is new to the base
  (`Dialect.sum.routes_of_names`). The round trip and well-formedness then
  hold for the sum with no new assumption. The sum of lawful dialects is
  lawful (`Dialect.sum.lawfulPoison`) when `e` accepts every type that the
  base accepts.
- **Tests.** The toy, use-once and probe test dialects are extensions of the
  core named `toy` with no types of their own. `lean/FirTest/Sum.lean` is
  gone.

This supersedes ADR-2026-10-30-2040.

## Alternatives

- **A list of dialects, indexed by name.** It fits any number of dialects
  at once. But typeclass search over a dependent family is fragile in Lean,
  and nested sums already hold any number.
- **Each extension routes its own types.** The sum would then trust the
  extension to send the base's types back to the base. Routing in the sum
  keeps the base's own rules on its types.

## Consequences

- An extension that depends on a dialect other than the whole base before
  it needs its classes lifted into a larger base. Stage 2 of #227 adds that.
- Core ops carry core types only. A value of an extension's own type cannot
  pass through a core `br`, `ret` or `call`. Lifting this needs the core's
  control ops to be generic in their types, which #227 does not cover.
- A module does not yet declare its dialect set in the text. Stage 4 of #227
  adds the declaration and the check on both sides.
