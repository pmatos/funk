# The spec sums a base dialect and an extension over it, routing ops and types by prefix

Status: accepted
Tier: direction; area: semantics

## Decision

- **An extension over a base.** An extension `e` has its own ops and types,
  and states each dialect class for `base.over e`, whose types are the
  base's and its own, so its ops take and give the base's values. Its
  memories are likewise the base's and its own (`DialectMemOver`).
- **The sum.** `base ⊞ e`, in `lean/Fir/Sum/`, has the ops and types of both,
  with each class lifted side by side. Its memories are `e`'s, and a base op's
  effects are renamed into them, so a memory has one name in the sum. Any
  number of dialects is a nested sum, `core ⊞ a ⊞ b`.
- **Routing.** A word belongs to the dialect named before its first `.`, a
  bare word to the core. Types go by their head word, attributes with their
  op.
- **Lifts.** An extension written over the dialects it depends on joins any
  sum that holds them: `e.lift dep ι μ` carries an inclusion `ι` of `dep`'s
  types in a larger base and a map `μ` of its memories. A lifted op sees only
  what `e` can write, under the human's #227 ruling of 2026-11-10 on
  ADR-2026-11-09-2353.
- **Laws.** The sum and the lift are lawful when their sides are, `e` writes
  its words under a name new to the base, and `e` accepts the types it
  depends on. Core ops carry core types only.
- **The set.** A module names the dialects of its sum on its first line
  (ADR-2026-11-10-1306).

[semantics-dialects.md](../decisions/semantics-dialects.md) states each rule
and the theorems.

## Why

ADR-2026-11-09-1543 combines a module's dialects as a sum routed by prefix.
Writing an extension over its base, and lifting it into a larger sum, lets
extensions written apart, such as a GPU dialect and a test dialect, share one
module, while the base keeps its own rules on its types and memories.

## Rejected alternatives

- **A plain sum, `Ty₁ ⊕ Ty₂`.** An extension's op could not take a core
  value, and the core's `i8` would have two spellings.
- **A list of dialects indexed by name.** Typeclass search over a dependent
  family is fragile in Lean, and nested sums hold any number.
- **Each extension routes its own types.** The sum would trust it to send the
  base's types back.
- **Each side's memories kept apart.** A memory of the base would have two
  names, and a pass could reorder accesses to it.
