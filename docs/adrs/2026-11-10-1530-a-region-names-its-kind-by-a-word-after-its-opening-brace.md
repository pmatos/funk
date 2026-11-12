# A region names its kind by a word after its opening brace

Status: accepted
Tier: direction; area: text-format

## Decision

- **The term.** A region holds its kind: `Region.kind : Option Name` in Lean,
  `Region::kind: Option<String>` in Rust. No kind is the core's kind, a
  control-flow graph of blocks whose ops run in order (ADR-2026-10-29-2005).
  A dialect's kind is a word of that dialect, such as `toy.graph`.
- **Spelling.** A region of an op writes its kind as a word right after its
  `{`, with one space: `toy.run { toy.graph`, then its blocks and `}`. A
  region of the core's kind writes nothing there, so every M0 text is
  unchanged.
- **Grammar.** `region ::= '{' word? block* '}'`. A block starts with a
  label, so the word is never read as anything else, and the lexer is
  unchanged.
- **A function's body** is a region of the core's kind, and its text names
  none, since a word after an item's `{` starts its items. Validation rejects
  a function whose body names a kind, which only a builder or a pass can
  make.
- **Well-formedness.** A region that names a kind names it by a word, so that
  the round trip holds.
- Which kinds an op may own, and each kind's rule, are validation's
  (ADR-2026-11-10-1941).

## Why

ADR-2026-11-09-1543 admits region kinds other than the core's control-flow
graph, such as unordered dataflow regions, and #230 asks that a region name
its kind, with the core's kind the default and every M0 text unchanged. A word
after `{` needs neither a second token of lookahead nor a new token.

## Rejected alternatives

- **The kind before the `{`.** For an op with no operands, a word there reads
  as an attribute until the `{` after it, so the parser would need a second
  token of lookahead.
- **The kind fixed by the owning op, not written,** as MLIR asks the op. #230
  asks that a region name its kind, and a reader would need the dialect to
  know how a region is read.
- **An attribute-like form, `{kind(toy.graph)`.** Longer, with no gain.
