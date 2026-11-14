# alloca allocates a constant count of values of a type on the stack of its memory

Status: accepted
Tier: direction; area: semantics

## Decision

- **The op.** `%p: ptr<N> = alloca KIND TYPE [COUNT] [align(A)]`, with no
  operands, for example `%p: ptr = alloca stack i32 4` and
  `%p: ptr(1) = alloca stack i8 12 align(4)`. Its attributes are separated by
  spaces, as every op's are. The count is written only when it is not 1, and
  `align(A)` only when the op gives an alignment, so each instance has one
  spelling. Its memory is the memory of its result.
- **Its meaning.** It allocates `COUNT` times the units that `TYPE` takes in
  memory `N`, with kind `KIND`, aligned to `A` units, or to the type's natural
  alignment when `A` is omitted: the least power of two that is at least the
  units the type takes (`MemLayout.intAlign`). The result has provenance for
  the allocation, at offset 0, and its units are poison. A stack allocation
  is freed when its call returns.
- **What M1 accepts.** Validation accepts the kind `stack` alone, a count of
  at least 1, a power of two for `A`, and a valid integer type. `global` and
  `heap` decode and are rejected, as hooks in the format
  (ADR-2026-11-09-1542).
- **Its poison and effects.** It is never UB and its result is never poison.
  Its effect set is "allocates in memory `N`".

## Why

The human ruled on 2026-11-14 (#378) that the op takes a type and a constant
count, that the kind is written and M1 accepts only `stack`, and that the
natural alignment of `iN` follows the pointer rule. The ruling's examples were
written with commas, `alloca stack i32, 4`. fir's text separates an op's
attributes by spaces and only its operands by commas (`add nuw nsw %a, %b`),
and a constant count is an attribute, so the spaces keep one attribute
grammar for every dialect.

## Rejected alternatives

- **Commas between the attributes.** The generic reader, its `fir-ref` copy
  and the Rust parser would need a second attribute grammar for one op.
- **A count of units.** It has no type to give a default alignment (the
  ruling).
- **A run-time count.** It needs may-UB for a poison count; #381 tracks it.
