# funk-ir holds ops as generic data and checks them through a registry of dialects

Status: accepted

## Context

G0 (ADR-2026-10-29-2016) requires that `funk-ir` represent an op
generically, checked through an op registry, and not as a closed Rust `enum`
of core ops, and that types be extensible the same way. Its list of an op's
parts lacks successors, which branch ops need. The spec lists them
(`Operation` in `lean/Fir/Syntax/Module.lean`): results, op instance,
operands, successors, regions and a location reference. A spec dialect
gives its ops' text (`DialectText`: `decodeOp` and `decodeTy`), signatures
(`DialectSignature`) and rules (`DialectValidation`). How real dialects
name their ops is H4, which is not decided.

## Decision

- **An op is data.** `funk_ir::Op` has, in the spec's order, `results`
  (names and types), `name`, `attrs`, `operands`, `succs` (labels and the
  values they pass), `regions` and `loc`. The name is a string; attributes
  (`Attr`) and types (`Type`, a word or a word applied to attributes) are
  generic terms, as the text writes them. `loc` is a `LocRef`, not an
  `Option`, so no op exists without a location.
- **Items follow the spec.** `Item` has one variant, `Func`, as the spec's
  `Item` has one constructor; it is `#[non_exhaustive]`. A module is the
  symbol table of its own items, so a nested module would be a new variant
  that holds a `Module`.
- **A registry of dialects.** A `Dialect` gives `OpSpec`s, one per op name,
  and `TypeSpec`s. `OpSpec::decode` takes an op's attributes and the types
  of its operands and results, and returns its `OpShape` (whether it is a
  terminator, how many successors it has, the symbols it refers to) or why
  it does not decode: the spec's `decodeOp` with the op's signature.
  `OpSpec::check` is the dialect's own rule (`validOp`). `TypeSpec::check`
  says whether a type decodes and whether it is valid (`decodeTy`,
  `validTy`). Registering rejects an op name that is not a word or that is
  already registered.
- **No per-op code outside the dialect.** The parser reads the one grammar,
  then decodes each op and type through the registry; a failure is a parse
  error (ADR-2026-10-30-0815). The printer writes every op the same way. The
  verifier looks up operand types and calls the same `decode`, so an op
  that a builder or a pass made ill-typed is a validation error.
- **One file per op family.** The core dialect is `dialects/core/`: its
  types in `types.rs`, and each op family in a file of its own, registered
  in `dialects/core/mod.rs`. The tracer registers `const`, `add` without
  flags and `ret`; each later family adds a file and one line.
- **A rule for test dialects, not a decision on H4.** A test-only dialect
  names its ops and types `toy.` followed by a word, such as `toy.br` and
  `toy.tok`. `.` is reserved for a dialect's name before its ops (H4), and
  no core op or type name contains one, so a test op never collides with a
  core op. A sum of the core and a test dialect routes each name that starts
  with `toy.` to the test dialect and every other name to the core; #10's
  Lean toy dialect routes by the same rule.

## Alternatives

- **A closed `enum` of core ops.** Ruled out by G0.
- **A decoded op instance stored in each op**, such as a trait object.
  Operand and result types would be held twice, in the instance and at the
  values' definitions, and could disagree. A name and attributes mirror the
  text and the spec's `opName` and `opAttrs`.
- **Interned or trait-object types.** More machinery than M0 needs. A type
  term has one spelling, so comparing terms compares types.

## Consequences

- A new dialect implements `OpSpec` and `TypeSpec` and registers; the IR,
  the parser, the printer and the verifier do not change. The test dialect
  in `crates/funk-ir/tests/toy.rs` shows it, with successors, regions, an
  applied attribute, a symbol reference and a type of its own.
- Checks that an `enum` would give for free, such as an op's operand count,
  live in each op's `decode`, and the parser and the verifier run them.
- Until its family lands, an op of the spec that the registry lacks, such as
  `sub` or `add nsw`, is a parse error in `funk`. Corpus texts use only
  registered ops.
- ADR-2026-10-29-2016 is refined by this ADR: an op's parts include its
  successors.
