# A region names its kind by a word after its opening brace

Status: accepted; refined by ADR-2026-11-10-1941
Tier: direction; area: text-format

## Context

ADR-2026-11-09-1543 decides that the format and the dialect classes admit
region kinds other than the core's control-flow graph, such as unordered
dataflow regions. [#230](https://github.com/pmatos/funk/issues/230) builds
it: a region names its kind, the core's kind is the default, and every M0
text stays unchanged. Stage 1 of #230 puts the kind in the terms and the
text. Which kinds exist, and their rules, are stage 2.

An op is written `name attr* operands region* @loc`, and an attribute may
be a bare word. An item's body is `{`, then items when a word follows, or
blocks ([#211](https://github.com/pmatos/funk/issues/211)).

## Decision

- **The term.** A region holds its kind: `Region.kind : Option Name` in
  Lean, `Region::kind: Option<String>` in Rust. No kind is the core's kind,
  a control-flow graph of blocks whose ops run in order
  (ADR-2026-10-29-2005). A dialect's kind is a word of that dialect, such
  as `toy.graph`.
- **Spelling.** A region of an op writes its kind as a word right after its
  `{`, with one space: `toy.run { toy.graph`, then its blocks and `}`. A
  region of the core's kind writes nothing there, so every M0 text is
  unchanged, byte for byte.
- **Grammar.** `region ::= '{' word? block* '}'`. A block starts with a
  label, so the word is never read as anything else. The line uses only
  existing tokens, so the lexer is unchanged.
- **A function's body** is a region of the core's kind, and its text names
  no kind, since a word after an item's `{` starts its items. Validation
  rejects a function whose body names a kind, which only a builder or a
  pass can make. A well-formed function's body names none.
- **Well-formedness.** A region that names a kind names it by a word, so
  that the round trip holds.
- **Validation is otherwise unchanged.** An op still owns no region, as in
  M0, so no text with a named kind is valid yet. Stage 2 lets a dialect
  register kinds with their rules.

## Alternatives

- **The kind before the `{`.** For an op with no operands, a word there
  reads as an attribute until the `{` after it, so the parser would need a
  second token of lookahead.
- **The kind fixed by the owning op, not written.** MLIR asks the op for
  its regions' kinds. #230 asks that a region name its kind, and a reader of
  the text would need the dialect to know how a region is read.
- **An attribute-like form, `{kind(toy.graph)`.** Longer, with no gain.

## Consequences

- The Lean reader, decoder, printer and their round-trip proofs, FirRef's
  loops with their `@[csimp]` proofs, and funk-ir's parser and printer
  carry the kind. Rust's well-formed generator names kinds, so the
  cross-language round trip covers them.
- A region kind's word does not yet join the dialect-set rule of
  ADR-2026-11-10-1306. It does when stage 2 lets a dialect register kinds.
