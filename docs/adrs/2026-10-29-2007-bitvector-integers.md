# Integers are bitvectors `iN` of any width, and signedness lives on ops

Status: accepted

## Context

This is decision S2 of the fir v0 decision record, agreed on 2026-10-29 and
stated in the M0 epic ([#5](https://github.com/pmatos/funk/issues/5)).

Frontends need different widths: C and C++ use 8 to 64 bits and `__int128`,
and C23's `_BitInt(N)` allows any width. Lean has `BitVec n` for every `n`, so
the semantics can treat every width alike. A machine supports only a few
widths natively.

## Decision

- fir integer types are bitvectors `iN`, for any width `N >= 1`.
- Signedness lives on ops, never on types: `sdiv` and `udiv`, `icmp slt` and
  `icmp ult`, and so on.
- `ptr` is a separate type. M0 reserves it and gives it no ops.
- The IR (`funk-ir`) and the Lean interpreter accept any `N >= 1`.
- The M0 backend supports `i1`, `i8`, `i16`, `i32`, `i64` and `i128`. `i128`
  lowers to register pairs, with division through a runtime helper. The
  backend rejects any other width with a clear diagnostic.
- These types belong to the core dialect, not to a closed type system (G0,
  ADR-2026-10-29-2016).

## Alternatives

- **Signed and unsigned integer types.** Rejected: signedness is a property of
  an operation, and one bit pattern is read both ways.

## Consequences

- Every op whose meaning depends on sign comes in a signed and an unsigned
  form.
- Odd widths, such as `i7` and `i33`, are tested on the interpreter only.
- The backend needs register pairs and a division helper for `i128`.
- Pointer ops wait for the memory model (S3), which is not decided.
