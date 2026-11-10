# A dialect registers region kinds, each with its own rule, and an op instance states its regions' kinds

Status: accepted
Tier: direction; area: validation

## Context

ADR-2026-11-09-1543 decides that the format and the dialect classes admit
region kinds other than the core's control-flow graph, such as unordered
dataflow regions. ADR-2026-11-10-1530, stage 1 of
[#230](https://github.com/pmatos/funk/issues/230), puts the kind in the
terms and the text, and leaves which kinds exist, and their rules, to stage
2. Until now an op owned no region: validation rejected every one. Nested
control-flow regions inside an op are structured control flow (H6), which
the M1 epic leaves out.

## Decision

- **An op instance states its regions' kinds.** `DialectSignature` gains
  `regionKinds : d.Op → List String`, empty by default; `OpShape` gains
  `regions` in Rust. A kind is a word of a dialect, never the core's kind:
  a region of the core's kind inside an op would be H6.
- **A dialect registers kinds, each with a rule.** `DialectValidation` gains
  `regionKindNames` and `validRegion`, with defaults of none and `False`,
  and `DecidableDialectValidation` decides it. The rule sees the region and
  the host function through a `DialectView` and a `FuncContext`, as
  `validFunc` does (ADR-2026-11-09-2257), so it is written once and holds in
  any sum. It says how values are scoped in a region of its kind, which ops
  end its blocks, and where its successors go. In Rust a dialect registers a
  `RegionKindSpec` with `Dialect::region_kind`.
- **Valid regions of an op** (`Func.RegionsValid`): the op owns one region
  for each kind its op instance states, in order; each kind is a word that
  the dialect registers; each region obeys its kind's rule. It replaces
  "the op owns no region" in `Func.OpValid`. No core op states a region, so
  every M0 text keeps its verdict.
- **Ops inside a region** obey the general rules that do not depend on the
  kind (`Func.InnerOpValid`, the field `inner` of `Func.Valid`): their
  regions, types, successor count, symbols, their dialect's own rule and
  their location. A successor's label is a name and the values it passes
  are defined in the function, so a valid function stays well formed. Where
  an op stands, where its successors go and which values it uses are the
  kind's rule. The check walks `Func.allBlocks` and each op's own regions,
  one level down, so it takes no stack per level of nesting.
- **The core's kind.** Its rule is the rule of a function's body, the
  existing premises of `Func.Valid`. The core registers no kind.
- **Sums and lifts.** The sum `base ⊞ e` registers the base's kinds then
  `e`'s, and sends a kind that the base registers to the base's rule, and
  any other to `e`'s, each through its own view. The lift registers `e`'s
  kinds with `e`'s rule through its view. `LawfulDialectSet` and
  `LawfulDialectName` ask that registered kinds be words of the dialect's
  name, so a kind goes to the dialect that registers it
  (`Dialect.sum.validRegion_ext`). In Rust, registration puts each kind
  under its dialect's prefix, as for ops (ADR-2026-11-10-0042), and
  rejects a kind of the core.
- **Dialect sets.** A region kind's word joins the words of ADR-2026-11-10-1306:
  `Operation.wordDialects` adds each region's kind after the op's name and
  attributes, so a kind of a dialect outside the module's set is rejected
  on both sides.
- **Running.** The interpreter runs only the core's kind: a function's body.
  An op that owns regions of a dialect's kinds runs by its dialect's
  semantics, as any op does, and the interpreter does not enter them. An op
  that owns a region of the core's kind leaves the path stuck
  (`Operation.ownsCoreRegion`); no valid op does, so the progress proofs
  hold. `fir-ref`'s machine has the same check.

## Alternatives

- **The owning op's dialect judges its regions.** Simpler routing, but a
  kind could not be shared: an op of a dialect that depends on `toy` could
  not own a `toy.graph` region checked by `toy`'s rule.
- **Ops may own regions of the core's kind.** That needs scoping and
  dominance across nested control-flow graphs, which is H6 and out of M1.
- **The kind's rule checks every op of its region.** A dialect cannot judge
  another dialect's op, so the general rules stay validation's.

## Consequences

- A dialect's semantics of an op that owns regions sees its op instance and
  operands only, not the region's terms. A kind whose regions run will need
  a hook that gives its semantics the region; no kind in M1 runs.
- Stage 3 of #230 builds a toy unordered kind on both sides, with shared
  cases and the G0 checks.
- ADR-2026-11-10-1530 and ADR-2026-11-10-1306 are refined.
