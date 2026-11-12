# funk-ir holds ops as generic data and checks them through a registry of dialects, routed by each word's dialect prefix

Status: accepted; refined by ADR-2026-11-09-1543
Tier: direction; area: rust-ir-and-tools

## Decision

- **An op is data.** `funk_ir::Op` has, in the spec's order, `results`,
  `name`, `attrs`, `operands`, `succs`, `regions` and `loc`. The name is a
  string; attributes and types are generic terms, as the text writes them.
  `loc` is a `LocRef`, so no op exists without a location. `Item` follows
  the spec's items and is `#[non_exhaustive]`.
- **A registry of dialects.** A `Dialect` gives `OpSpec`s, one per op name,
  and `TypeSpec`s. `OpSpec::decode` takes an op's attributes and the types
  of its operands and results, and returns its `OpShape` or why it does not
  decode: the spec's `decodeOp` with the op's signature. `OpSpec::check` is
  the dialect's own rule. `TypeSpec::check` says whether a type decodes and
  whether it is valid.
- **No per-op code outside the dialect.** The parser reads the one grammar,
  then decodes each op and type through the registry; a failure is a parse
  error (ADR-2026-10-29-2014). The printer writes every op the same way. The
  verifier calls the same `decode`, so an op that a builder or a pass made
  ill-typed is a validation error. A new dialect implements `OpSpec` and
  `TypeSpec` and registers; the IR, parser, printer and verifier do not
  change.
- **A word names its dialect.** The part of a word before its first `.`
  names its dialect, and a bare word is the core's. A dialect's name is a
  word with no `.`. Registration rejects an op name that is not a word, is
  already registered, or is not written under its dialect's name, so a core
  op is bare and a `toy` op is `toy.` and a word. A type goes only to the
  `TypeSpec`s of the dialect its head word names, so no dialect can claim
  another's type.
- **Dependencies.** A dialect names the dialects whose types its ops may
  take. Registration rejects a dependency that is not yet registered, so
  dependencies form no cycle. A module's dialect set is to use them; no
  check does yet. A failed registration changes nothing.

## Why

G0, set by the human on 2026-10-29 (ADR-2026-10-29-2016), requires that
`funk-ir` represent an op generically, checked through a registry, and not
as a closed Rust `enum`, with types extensible the same way. The spec's
dialects give their ops' text, signatures and rules, and the registry
mirrors them. ADR-2026-11-09-1543 makes every dialect but the core write
its words as `name.word`, and routing by that prefix keeps each op and type
with its own dialect.

## Rejected alternatives

- **A closed `enum` of core ops.** Ruled out by G0.
- **A decoded op instance stored in each op**, such as a trait object.
  Operand and result types would be held twice and could disagree.
- **Interned or trait-object types.** A type term has one spelling, so
  comparing terms compares types.
- **Each `TypeSpec` lists the head words it decodes.** The core's `iN` is
  an infinite family, and routing already gives the guarantee.
- **A map per dialect, looked up after the prefix.** The flat map gives the
  same answer with one hash per op, on funk's hot path.
