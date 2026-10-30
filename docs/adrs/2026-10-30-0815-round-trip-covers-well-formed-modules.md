# The round trip covers well-formed modules, and text that does not decode is a parse error

Status: accepted

## Context

P3 (ADR-2026-10-29-2014) requires `parse(print(m)) == m` for every module
`m`. The fir v0 spec ([#8](https://github.com/pmatos/funk/issues/8)) writes
every op in one generic form, with types only where values are defined
(`%x: i32`). A parser finds an op's operand types at the definitions of its
operands. So an op whose operand is not defined, or has the wrong type, has
no text that reads back to it, and the round trip cannot hold for every
module.

The human ruled on 2026-10-30 to narrow P3, rather than write a full
signature on every op (choice 1 in the
[rulings comment](https://github.com/pmatos/funk/issues/5#issuecomment-6506908304) on #5, part 1).

## Decision

- `parse(print(m)) == m` holds for every well-formed module: one whose
  printed form says everything it holds. The spec defines it as
  `Module.WellFormed` in `lean/Fir/Text/RoundTrip.lean`.
  `print(parse(t)) == t` holds for every text printed from one.
- Every valid module is well formed. Validation checks the characters of
  value names and labels and the limits on numbers, and symbols that are not
  words are quoted, so two different valid modules never print the same
  text. #11 proves this for the core dialect.
- A text that follows the grammar but does not decode is not a module. The
  parser rejects it with a reason and a position: a number out of range, a
  string or symbol not in its one spelling, an item of an unknown kind, a
  type that does not decode, a value defined twice, an operand that is not
  defined, or an op whose name, attributes and types do not decode, such as
  a type mismatch.
- Every other error, such as an undefined successor argument, is a
  validation error on a module that parsed.

## Alternatives

- **A full signature on every op**, as MLIR's generic form writes it
  (`: (i32, i32) -> i1`). Every module would round-trip, ill-typed ones
  included, and type errors would be validation errors. Rejected: every type
  would be written twice, and op lines would grow long.

## Consequences

- Lean's and Rust's parsers must reject the same texts. Tests compare only
  whether a text is rejected, not the wording of the reason.
- A type mismatch or an undefined operand is a parse error, so its tests are
  parser tests (#9, #10, #13, #20), not verifier tests.
- The rest of ADR-2026-10-29-2014 stands.
