# alloca allocates a constant count of values of a type on the stack of its memory

Status: accepted
Tier: direction; area: semantics

## Decision

- **The op.** `%p: ptr<N> = alloca KIND TYPE [COUNT] [align(A)]`, with no
  operands, for example `%p: ptr(1) = alloca stack i8 12 align(4)`. Its
  attributes are separated by spaces. The count is written only when it is
  not 1, and `align(A)` only when given, so each instance has one spelling.
  Its memory is its result's.
- **Its meaning.** It allocates `COUNT` times the units of `TYPE` in memory
  `N`, with kind `KIND`, aligned to `A` units, or to the type's natural alignment
  (`MemLayout.intAlign`). The result has provenance for the allocation at
  offset 0, whose units are poison. A stack allocation is freed when its call
  returns. It is never UB, its result is never poison, and its effect is
  "allocates in memory `N`".
- **What M1 accepts.** The kind `stack` alone (`global` and `heap` decode, as
  hooks: ADR-2026-11-09-1542), a count of at least 1, a power of two `A` no
  larger than `MemLayout.limit` (2^24 - 1), which bounds a written `A` only
  (#385), and a valid integer type. The count has no bound: one too large
  for the machine is a resource error at run time, as a deep recursion is.

## Why

The human ruled on 2026-11-14 (#378): a type and a constant count, a written
kind with `stack` alone in M1, and the natural alignment of `iN` by the
pointer rule. On 2026-11-14 (#382) the human confirmed the spaces, one
attribute grammar for every dialect, and ruled: integer elements until float
and pointer loads and stores land; `A` bounded as the layout line bounds its
own alignments, the count unbounded; and the G0 check's exemption of `align`
kept
(semantics-m1-memory.md).

## Rejected alternatives

- **Commas between the attributes:** a second attribute grammar for one op.
- **A count of units:** no type to give a default alignment.
- **A run-time count:** it needs may-UB for a poison count (#381).
- **A bound on the count:** it would not keep an allocation within a
  machine, since one `i16777215` takes 2 MiB.
