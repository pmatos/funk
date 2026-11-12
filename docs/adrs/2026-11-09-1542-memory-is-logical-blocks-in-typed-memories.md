# Memory is logical blocks in typed memories, and a pointer becomes an integer only by explicit exposure

Status: accepted
Tier: direction; area: semantics

## Decision

- **Logical blocks.** A pointer is an allocation id and an offset. Memory
  maps each allocation to an array of abstract units, each concrete bits,
  poison or a fragment of a pointer. Fresh memory holds poison. An access out
  of bounds, after its allocation is freed, or through a pointer without
  provenance for that allocation is immediate UB.
- **Explicit exposure.** `ptr.expose` turns a pointer into an integer and
  marks its allocation exposed. `ptr.from_int` turns an integer back into a
  pointer, with the provenance of an exposed allocation that contains the
  address. No other op converts between pointers and integers.
- **Typed memories.** A pointer type names its memory: the core `ptr` is
  memory 0, and a dialect may add memories of its own, such as the GPU
  dialect's shared memory (ADR-2026-11-09-1545). A pointer moves
  between memories only through an op that a dialect provides. The module's
  data layout gives each memory its unit of addressing, 8-bit bytes unless it
  says otherwise, and its pointer width.
- **Addresses in `fir-ref`.** Only exposed allocations have integer
  addresses, assigned from one canonical layout, so exhaustive mode stays
  finite. A test whose observations depend on an exposed address is
  interpreter-only.
- **Hooks.** Memory ops carry an `ordering` attribute, and M1 accepts only
  `nonatomic`. Allocations carry a kind: stack, global or heap.

[semantics-m1-design.md](../decisions/semantics-m1-design.md) states each
rule. The human ruled this on 2026-11-09, on #206.

## Why

It follows where Rust's strict and exposed provenance and recent LLVM work
converge. Optimizations may assume that distinct allocations do not alias,
unless a pointer was exposed and rebuilt from an integer. G0 asks for several
memories and address spaces, and the hooks let a concurrency model and managed
memory come later without a format change.

## Rejected alternatives

- **Flat, concrete memory.** Pointers would be integers. Every allocation's
  address would become a choice, which explodes exhaustive runs and blocks
  most alias reasoning.
- **Logical blocks without integer casts in M1.** C and kernel code that
  casts pointers could not be lowered in M1, against the scope of
  ADR-2026-11-09-1548.
