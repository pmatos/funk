# A pointer moves by ptradd, by a signed integer of any width, in units of its memory

Status: accepted
Tier: direction; area: semantics

## Decision

- **The op.** `ptradd` takes a `ptr<N>` and an `iW` of any width `W`, in
  that order, and gives a `ptr<N>` of the same memory. It is written
  `%q: ptr = ptradd %p, %k`, with no attributes. Any other shape does not
  decode.
- **Its meaning.** The result keeps the pointer's provenance, and its
  offset is the pointer's offset plus the integer, read as signed, in units
  of the memory `N` (ADR-2026-11-09-1542). The offset is a mathematical
  integer: it never wraps, and it may leave the allocation in either
  direction. Only an access through the result must be in bounds.
- **Its poison and effects.** A poison operand gives a poison result, and
  defined operands give a defined pointer. It is never UB, so its effect set
  is empty: it is pure.
- **No flags.** No `inbounds`, `nuw` or `nsw` in M1.

## Why

#231 asks for pointer offset arithmetic. Logical blocks give a pointer an
allocation and an offset in units, so moving a pointer changes the offset
alone, and needs neither the data layout nor memory: the op is pure, and
passes may move or remove it freely. A signed integer of any width lets a
frontend pass its index as it has it. A native backend adds the integer,
sign-extended or cut to the pointer's width; the address it computes wraps
where the spec's offset does not, but the two agree on every access the
spec allows, since such an access lands in bounds.

## Rejected alternatives

- **An offset of the pointer's width only.** Validation would need the
  module's data layout at every op, and frontends would widen or cut every
  index first.
- **UB when the result leaves its allocation, or poison as with LLVM's
  `inbounds`.** C allows a pointer one past the end, and code that moves a
  pointer out and back is common; a flag that promises in-bounds results can
  be added when an optimization needs it.
- **A typed element size, as LLVM's `getelementptr` has.** The aggregate
  layouts of ADR-2026-11-09-1550 compute field addresses; `ptradd` counts
  units, as LLVM's own `ptradd` does.
