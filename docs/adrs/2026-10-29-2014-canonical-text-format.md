# fir has one canonical text format, and the printer is the formatter

Status: accepted
Tier: direction; area: text-format

## Decision

- fir has one canonical text form: no sugar, no alternative spellings. The
  grammar has exactly one spelling for every construct.
- The printer is the formatter: `funk fmt` prints a module in canonical form.
- Value names, attributes and locations are stored in the IR and printed as
  stored. Nothing is renumbered.
- The text format is the interface between Lean and Rust: Rust prints a
  module, Lean parses and reprints it, and the bytes must match.
- Every op of every dialect uses one grammar, so a new dialect needs no parser
  change (G0, ADR-2026-10-29-2016).
- `parse(print(m)) == m` holds for every well-formed module: one whose printed
  form says everything it holds (`Module.WellFormed` in
  `lean/Fir/Text/RoundTrip.lean`). `print(parse(t)) == t` holds for every text
  printed from one. Every valid module is well formed.
- A text that follows the grammar but does not decode is not a module. The
  parser rejects it with a reason and a position: a number out of range, a
  string or symbol not in its one spelling, an item of an unknown kind, a
  type that does not decode, a value defined twice, an operand that is not
  defined, or an op whose name, attributes and types do not decode, such as
  a type mismatch. Every other error is a validation error on a module that
  parsed. Lean's and Rust's parsers reject the same texts.
- Text is fir's only format in v0.

## Why

Two independent implementations, the Rust toolchain and the Lean semantics,
read and write fir, and comparing bytes is the simplest check that they agree.
Agents read, write and diff fir text, which is easiest when a module has one
spelling, and a module that keeps its producer's names diffs small.

Text writes types only where values are defined, so a parser finds an op's
operand types at its operands' definitions. An op whose operand is undefined
or ill-typed has no text that reads back to it. The human chose P3 on
2026-10-29 (#5), and on 2026-10-30 narrowed its round trip to well-formed
modules rather than write a signature on every op (choice 1 of the rulings on
#5).

## Rejected alternatives

- **Sugar or alternative spellings.** Each breaks `print(parse(t)) == t` or
  needs a normalizing step in both implementations.
- **A full signature on every op**, as MLIR's generic form writes it, so that
  ill-typed modules round-trip too. Every type would be written twice and op
  lines would grow long.
- **A binary format.** Left out on purpose; it can come if text parsing
  becomes a bottleneck.
