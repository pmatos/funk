# fir has one canonical text format, and the printer is the formatter

Status: accepted

## Context

This is decision P3 of the fir v0 decision record, agreed on 2026-10-29 and
stated in the M0 epic ([#5](https://github.com/pmatos/funk/issues/5)).

Two independent implementations read and write fir: the Rust toolchain and the
Lean semantics (S7, ADR-2026-10-29-2009). They must agree on every module, and
comparing bytes is the simplest check that they do. Agents also read, write and
diff fir text, which is easiest when one module has one spelling.

## Decision

- fir has one canonical text form: no sugar, no alternative spellings.
- The printer is the formatter: `funk fmt` prints a module in canonical form.
- Value names, attributes and locations are stored in the IR and printed as
  stored. Nothing is renumbered.
- `print(parse(t)) == t` for every printed `t`, and `parse(print(m)) == m` for
  every module `m`.
- The text format is the interface between Lean and Rust: Rust prints a
  module, Lean parses and reprints it, and the bytes must match.
- Every op of every dialect uses one grammar, so a new dialect needs no parser
  change (G0, ADR-2026-10-29-2016).

## Alternatives

- **Sugar or alternative spellings.** Rejected: each extra spelling breaks
  `print(parse(t)) == t` or needs a normalizing step in both implementations.

## Consequences

- The grammar has exactly one spelling for every construct.
- Round trips are tested within Rust and across Rust and Lean, including
  under fuzzing, and Lean proves that parsing a printed module gives it back.
- A module keeps the names its producer gave it, so diffs between versions
  stay small and diagnostics name values as the author wrote them.
- Text is fir's only format in v0. A binary format is left out on purpose, and
  can come later if text parsing becomes a bottleneck.
