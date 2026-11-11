# The world may create and free heap allocations when it answers an external call

Status: accepted
Tier: direction; area: semantics

## Context

ADR-2026-11-09-1542 gives allocations a kind, and heap allocations come
through external calls. ADR-2026-11-09-1548 keeps heap allocation a call to
an external function such as `malloc`, with no op of its own. But the world
of ADR-2026-11-09-1540 only gives a call's results and writes into memory
that has escaped to it, so it has no way to create an allocation
([#251](https://github.com/pmatos/funk/issues/251)). The human ruled on #251
on 2026-11-11.

## Decision

- **Creating.** When the world answers an external call, it may create fresh
  allocations of kind heap, in a named memory.
- **Freeing.** It may free heap allocations that have escaped to it.
- **Handing them over.** It may return pointers into the allocations it
  creates, and write such pointers into escaped memory. A fresh allocation
  has escaped to the world from the start.
- **`malloc` stays external.** `malloc`, `free` and their kin are ordinary
  external declarations, as decided on
  [#201](https://github.com/pmatos/funk/issues/201) (ADR-2026-11-09-1548).
  No op allocates on the heap.

This refines the world of ADR-2026-11-09-1540. It agrees with
ADR-2026-11-09-1542 and ADR-2026-11-09-1548.

## Alternatives

- **Heap ops in the core.** ADR-2026-11-09-1548 rejected them, and C code
  calls allocators that funk does not know by name.

## Consequences

- A test's script can create and free heap allocations as part of an
  external call's answer.
- Once an access reaches a heap allocation that the world freed, the usual
  rule applies: an access to a freed allocation is UB (ADR-2026-11-09-1542).
- The memory tickets build it in the spec and `fir-ref`
  ([#233](https://github.com/pmatos/funk/issues/233)), and the calls to C
  ticket in native runs ([#239](https://github.com/pmatos/funk/issues/239)).
