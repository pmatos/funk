# Memory is logical blocks in typed memories, and a pointer becomes an integer only by explicit exposure

Status: accepted

## Context

This is decision S3 of the fir v0 decision record, which marks it
Foundational. M0 reserves the type `ptr` but gives it no values and no ops.
G0 (ADR-2026-10-29-2016) asks for several memories and address spaces.
The record's proposal follows where Rust's strict and exposed provenance
and recent LLVM work converge. The human ruled on
[#206](https://github.com/pmatos/funk/issues/206) on 2026-11-09, after
ADR-2026-11-09-1322 fixed the behaviour that memory builds on.

## Decision

- **Logical blocks.** A pointer is an allocation id and an offset. Memory
  maps each allocation to an array of abstract units. Each unit is
  concrete bits, poison, or a fragment of a pointer. Fresh memory holds
  poison.
- **Immediate UB.** An access out of bounds, after its allocation is
  freed, or through a pointer without provenance for that allocation is
  immediate UB.
- **Explicit exposure.** `ptr.expose` turns a pointer into an integer and
  marks its allocation exposed. `ptr.from_int` turns an integer back into a
  pointer, with the provenance of an exposed allocation that contains the
  address. No other op converts between pointers and integers.
- **Typed memories.** A pointer type names its memory: the core `ptr` is
  `ptr<0>`, other memories are `ptr<N>`, and a dialect may add memories of
  its own. A pointer moves between memories only through an op that a
  dialect provides.
- **Units and widths per memory.** The module's data layout gives each
  memory its unit of addressing, 8-bit bytes unless it says otherwise, and
  its pointer width. Sizes and offsets in a memory count its units.
- **Addresses in `fir-ref`.** Only exposed allocations have integer
  addresses. `fir-ref` assigns them from one canonical layout: in
  allocation order, aligned, deterministic. That is one of the address
  assignments the spec allows, so exhaustive mode stays finite. A test
  whose observations depend on an exposed address is interpreter-only, and
  the harness never compares raw addresses.
- **Hooks from the start.**
  - Memory ops carry an `ordering` attribute. M1 accepts only
    `nonatomic`, so a concurrency model (S6) needs no format change.
  - Allocations carry a kind: stack (ADR-2026-11-09-1548), global
    (ADR-2026-11-09-1546), and heap through external calls. Managed memory
    can be added as another kind later.
- **Effects and observations.** Loads, stores and allocation name their
  memory (ADR-2026-11-09-1541). An observer sees memory as
  ADR-2026-11-09-1540 says.
- **`ptr` has values.** Every theorem that relies on `ptr` having none is
  restated. Call congruence is the first
  ([#214](https://github.com/pmatos/funk/issues/214)).

## Alternatives

- **Flat, concrete memory.** Pointers would be integers. Native runs would
  be easy to match, but every allocation's address would become a choice,
  which explodes exhaustive runs and blocks most alias reasoning.
- **Logical blocks without integer casts in M1.** C and kernel code that
  casts pointers could not be lowered until a later milestone, which
  contradicts the scope set by ADR-2026-11-09-1548.

## Consequences

- Optimizations may assume that distinct allocations do not alias, unless
  a pointer was exposed and rebuilt from an integer.
- `fir-ref` covers one address assignment, not all of them. Programs whose
  results depend on addresses are judged by `fir-ref` alone.
- The GPU dialect's shared memory (ADR-2026-11-09-1545) is a memory of
  this model.
