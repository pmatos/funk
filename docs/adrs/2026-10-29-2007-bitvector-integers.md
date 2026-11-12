# Integers are bitvectors `iN` within MLIR's limits, and signedness lives on ops

Status: accepted
Tier: direction; area: semantics

## Decision

- fir integer types are bitvectors `iN`, for `1 <= N <= 16,777,215`, which
  is `2^24 - 1`. The IR (`funk-ir`) and the Lean interpreter accept every
  width in that range, and a wider type does not decode in either.
- Signedness lives on ops, never on types: `sdiv` and `udiv`, `icmp slt` and
  `icmp ult`, and so on.
- Pointer types are separate from integers (ADR-2026-11-09-1542). These types
  belong to the core dialect, not to a closed type system (G0,
  ADR-2026-10-29-2016).
- Every other number that gives the text its structure is below `2^32`: a
  location reference, a line and a column. An integer attribute has no bound
  of its own; the dialect that reads it bounds it, as a core constant must
  fit its type. A number out of its range is a parse error, located at the
  number.
- The M0 backend supports `i1`, `i8`, `i16`, `i32`, `i64` and `i128`.
  `i128` lowers to register pairs, with division through a runtime helper.
  The backend rejects any other width with a clear diagnostic, and odd
  widths are tested on the interpreter only.

This is S2 of the fir v0 decision record, agreed on 2026-10-29 (#5). The
bounds are N3, MLIR's limits, which the human ruled on 2026-10-30 (part 3 of
the rulings comment on #5). [semantics.md](../decisions/semantics.md) states
what holds.

## Why

Frontends need different widths: C and C++ use 8 to 64 bits and `__int128`,
and C23's `_BitInt(N)` allows any width. Lean has `BitVec n` for every `n`,
so the semantics treats every width alike. Every tool holds a width in 24
bits and a location reference, a line or a column in 32, as MLIR does, and a
frontend that needs a wider integer splits it.

## Rejected alternatives

- **Signed and unsigned integer types.** Signedness is a property of an
  operation, and one bit pattern is read both ways.
- **Any width `N >= 1`, with no bound,** as S2 first said. No tool can hold
  every width, line or location reference in an integer of fixed width.
