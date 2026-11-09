# Dialects extend fir through prefixed names, registered kinds of item and a dialect set that each module declares

Status: accepted
Tier: direction; area: semantics

## Context

This is decision H4 of the fir v0 decision record, which marks it
Foundational. M0 already makes ops and types data: a registry of dialects
in Rust (ADR-2026-10-30-1146) and typeclasses in Lean (G0,
ADR-2026-10-29-2016). Combining dialects exists only for tests: a sum that
routes names starting with `toy.` to a test dialect over shared types
(ADR-2026-10-30-2040), which says it decides nothing about H4. A module
holds functions only, and a new kind of item needs a parser change
(ADR-2026-11-03-0600). Modules declare no dialects, though the record's P3
and H5 say they should. The human ruled on
[#202](https://github.com/pmatos/funk/issues/202) on 2026-11-09.

## Decision

- **Prefixed names.** Every dialect other than the core writes its ops,
  types and attributes as `name.word`. Core words stay bare.
- **Sums of dialects.** A module's dialects combine as a sum routed by the
  prefix, for ops, types and attributes alike. The sum moves from
  `lean/FirTest/` into the spec. A dialect declares the dialects it depends
  on, and may name their types, which is how an extension op takes a core
  value.
- **Kinds of item.** A dialect registers kinds of item through the one
  grammar, as it registers ops, so a new kind needs no parser change. The
  core registers `func`, `global` (ADR-2026-11-09-1546), external
  declarations (ADR-2026-11-09-1547) and `module`. A `module` item holds a
  nested symbol table, so nested and device modules exist
  ([#211](https://github.com/pmatos/funk/issues/211)).
- **A dialect set per module.** Each module declares the dialects it uses.
  The verifier rejects any op, type, attribute or kind of item from a
  dialect outside the set. A nested module declares its own set, which is
  how a host module holds a device module.
- **Region kinds.** The format and the dialect classes admit region kinds
  other than the core's CFG region, such as unordered dataflow regions
  (G0, E0 in ADR-2026-10-29-2005). No other kind is built in M1.
- **Effects and observations** come from the dialect too
  (ADR-2026-11-09-1541, ADR-2026-11-09-1540).

## Alternatives

- **Every extension must have a verified lowering to core,** as the record
  proposed. A quantum or photonic dialect cannot lower to a CPU-shaped
  core, so this would fail G0. ADR-2026-11-09-1544 replaces it.
- **A fixed list of kinds of item in the core.** Less machinery, but every
  new kind would be a core change.

## Consequences

- The toy routing rule becomes the general rule, and test dialects keep the
  `toy.` prefix.
- The round-trip and validation proofs are restated over sums of dialects
  and over registered kinds of item.
- Every existing module needs a dialect set. A module that declares none
  uses the core alone, so M0's texts stay valid.
