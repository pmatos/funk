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
  at least 1, a power of two for `A` no larger than `MemLayout.limit`
  (2^24 - 1, so 2^23 at most), and a valid integer type. `global` and `heap`
  decode and are rejected, as hooks in the format (ADR-2026-11-09-1542).
  The count has no bound: one too large for the machine is a resource
  error at run time, as a deep recursion is.
- **Its poison and effects.** It is never UB and its result is never poison.
  Its effect set is "allocates in memory `N`".

## Why

The human ruled on 2026-11-14 (#378) that the op takes a type and a constant
count, that the kind is written and M1 accepts only `stack`, and that the
natural alignment of `iN` follows the pointer rule. On 2026-11-14 (#382) the
human confirmed the spaces, which keep one attribute grammar for every
dialect (`add nuw nsw %a, %b`); kept integer types until float and pointer
loads and stores land; bounded the alignment as the layout line bounds its
own and left the count unbounded; and kept the G0 check's exemption of
`align`, which the generic layout line writes too.

## Rejected alternatives

- **Commas between the attributes,** as #378's examples wrote them: a second
  attribute grammar for one op.
- **A count of units.** It has no type to give a default alignment.
- **A run-time count.** It needs may-UB for a poison count; #381 tracks it.
- **A bound on the count.** It would not keep an allocation within a
  machine: one `i16777215` takes 2 MiB.
- **G0 reading only the core and type text,** which checks no `alloca` word.
