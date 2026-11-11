# An inline assembly block is an event of the trace only when its effect set says observable

Status: accepted
Tier: direction; area: semantics

## Context

ADR-2026-11-09-1552 gives an inline assembly block an explicit effect set,
observable or not, yet says that running a block is always an event of the
trace. ADR-2026-11-09-1541 says that an op without observable adds no event,
and classifies inline assembly as observable. The two cannot both hold for a
block whose effect set leaves out observable
([#251](https://github.com/pmatos/funk/issues/251)). The human ruled on #251
on 2026-11-11.

## Decision

- **The effect set decides.** An inline assembly block is observable only
  when its effect set says so.
- **Without observable,** a block adds no event to the trace. Passes may
  delete it, merge it with an equal block or move it, within its declared
  reads and writes. This is GCC's plain `asm`.
- **With observable,** running the block is an event of the trace, as
  ADR-2026-11-09-1552 has it. This is GCC's `asm volatile`.
- **Its answer.** Either way the block takes its answer from the world
  (ADR-2026-11-09-1552). For a block without observable, the world's answer
  is keyed by the block and its operands, not by its position in the trace.
  So the same block on the same operands gets the same answer wherever it
  runs.
- **The classification.** ADR-2026-11-09-1541 classifies inline assembly as
  observable unless its effect set says otherwise. Its proof obligation stands:
  an op without observable adds no event.

This refines ADR-2026-11-09-1552's semantics and ADR-2026-11-09-1541's
classification.

## Alternatives

- **Every block is an event.** The effect set's observable would mean
  nothing for inline assembly, and passes could never remove a block that
  only computes, as GCC does.

## Consequences

- A frontend maps C's `asm` to a block without observable and `asm volatile`
  to one with it.
- A test's script answers an unobservable block by the block and its
  operands, and an observable one in trace order, as for external calls.
- The inline assembly ticket ([#240](https://github.com/pmatos/funk/issues/240))
  builds this rule.
