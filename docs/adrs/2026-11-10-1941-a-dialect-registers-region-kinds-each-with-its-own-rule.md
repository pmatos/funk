# A dialect registers region kinds, each with its own rule, and an op instance states its regions' kinds

Status: accepted
Tier: direction; area: validation

## Decision

- **An op instance states its regions' kinds.** `DialectSignature` has
  `regionKinds : d.Op → List String`, empty by default; `OpShape` has
  `regions` in Rust. A kind is a word of a dialect, never the core's kind:
  a region of the core's kind inside an op would be structured control flow
  (H6), which M1 leaves out.
- **A dialect registers kinds, each with a rule.** `DialectValidation` has
  `regionKindNames` and `validRegion`, by default none and `False`, and
  `DecidableDialectValidation` decides it. The rule sees the region and the
  host function through a `DialectView` and a `FuncContext`, as `validFunc`
  does (ADR-2026-11-09-2257). It says how values are scoped in a region of
  its kind, which ops end its blocks and where its successors go. In Rust a
  dialect registers a `RegionKindSpec` with `Dialect::region_kind`, under
  its prefix (ADR-2026-11-10-0042), and a kind of the core is rejected.
- **Valid regions** (`Func.RegionsValid`): an op owns one region per kind
  its op instance states, in order; each kind is registered; each region
  obeys its kind's rule. No core op states a region.
- **Ops inside a region** obey the general rules that do not depend on the
  kind (`Func.InnerOpValid`): their regions, types, successor count,
  symbols, their dialect's own rule and their location. A successor's label
  is a name and the values it passes are defined in the function. Where an
  op stands, where its successors go and which values it uses are the
  kind's rule. The check walks each op's own regions one level down, so it
  takes no stack per level.
- **The core's kind** is a function's body, and its rule is the rest of
  `Func.Valid`. The core registers no kind.
- **Sums and lifts.** `base ⊞ e` registers the base's kinds then `e`'s, and
  sends a kind that the base registers to the
  base's rule and any other to `e`'s, each through its own view; a lift
  registers `e`'s kinds. `LawfulDialectSet` and `LawfulDialectName` ask that
  kinds be words of the dialect's name (`Dialect.sum.validRegion_ext`).
- **Dialect sets.** `Operation.wordDialects` adds each region's kind, so a
  kind of a dialect outside the module's set is rejected on both sides
  (ADR-2026-11-10-1306).
- **Running.** The interpreter runs only the core's kind. An op that owns
  regions of a dialect's kinds runs by its dialect's semantics, which sees
  its op instance and operands, not the regions. An op that owns a region
  of the core's kind leaves the path stuck (`Operation.ownsCoreRegion`); no
  valid op does. `fir-ref`'s machine has the same check. A kind whose
  regions run will need a hook that gives its semantics the region.

This refines ADR-2026-11-10-1530 and ADR-2026-11-10-1306.

## Why

Kinds other than the core's control-flow graph, such as unordered dataflow
regions, are admitted (ADR-2026-11-09-1543). Routing by the kind's dialect
lets one dialect's ops own another's kinds, and a rule over a view holds in
any sum.

## Rejected alternatives

- **The owning op's dialect judges its regions.** A kind could not be
  shared: an op of a dialect that depends on `toy` could not own a
  `toy.graph` region checked by `toy`'s rule.
- **Ops may own regions of the core's kind.** That needs scoping and
  dominance across nested control-flow graphs, which is H6 and out of M1.
- **The kind's rule checks every op of its region.** A dialect cannot judge
  another dialect's op, so the general rules stay validation's.
