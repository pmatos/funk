# Dialects extend fir through prefixed names, registered kinds of item and a dialect set that each module declares

Status: accepted; refined by ADR-2026-11-10-1510
Tier: direction; area: semantics

## Decision

- **Prefixed names.** Every dialect other than the core writes its ops,
  types, attributes and kinds of item as `name.word`. Core words stay bare.
- **Sums of dialects.** A module's dialects combine as a sum routed by the
  prefix, for ops, types and attributes alike. A dialect declares the
  dialects it depends on, and may name their types, which is how an
  extension op takes a core value. ADR-2026-11-09-2306 says how the spec
  builds the sum.
- **Kinds of item.** A dialect registers kinds of item, each a word of its
  own with its own rule, written by the one item production with an empty
  body, so a new kind needs no parser change. The core's `func` and `module`
  are terms of their own, and a `module` item nests a symbol table.
- **A dialect set per module.** Each module declares the dialects it uses,
  and the verifier rejects any op, type, attribute or kind of item from a
  dialect outside the set. A nested module declares its own set, which is how
  a host module holds a device module. A module that declares none uses the
  core alone.
- **Region kinds.** The format and the dialect classes admit region kinds
  other than the core's CFG region, each registered by a dialect with its own
  rule.
- **Effects and observations** come from the dialect too.

[semantics-dialects.md](../decisions/semantics-dialects.md) states what holds.
The human ruled this on 2026-11-09, on #202.

## Why

G0 asks that fir reach hardware that M0 does not target. Ops and types were
already data, in Rust's registry and Lean's classes; prefixed names, sums and
registered kinds let a dialect add types, attributes and items as well, with
no change to the core, the grammar or the parser. A declared set makes what a
module may use checkable.

## Rejected alternatives

- **Every extension must have a verified lowering to core,** as the decision
  record proposed. A quantum or photonic dialect cannot lower to a CPU-shaped
  core, so this would fail G0 (ADR-2026-11-09-1544).
- **A fixed list of kinds of item in the core.** Every new kind would be a
  core change.
- **A typed item instance per dialect,** with a decoder and round-trip laws.
  It changes the structure every dialect builds, and no M1 kind needs more
  than attributes and a signature.
