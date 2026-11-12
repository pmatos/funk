# Inline assembly is an op tagged with its target, answered by the world, and an event only when its effect set says observable

Status: accepted
Tier: direction; area: semantics

## Decision

- **Shape.** An op tagged with its target, holding a template, constraints,
  operands, results, clobbers and an explicit effect set
  (ADR-2026-11-09-1541). A module for another target rejects it.
- **The effect set decides.** With observable, running the block is an event
  of the trace (ADR-2026-11-09-1540), as GCC's `asm volatile` is. Without it,
  the block adds no event, as GCC's plain `asm`: passes may delete it, merge
  it with an equal block or move it within its declared reads and writes. They
  merge or move it only when no write to the memories it reads comes between,
  a write by the block itself included.
- **The answer.** The world answers a block with its results and with the
  writes its declared effects allow. An observable block is answered in trace
  order. One without observable is answered by the block, its operands and the
  contents of the memories it declares it reads, so the same block on the same
  inputs gets the same answer wherever it runs. `fir-ref` takes the answer
  from the test's script.
- **In M1:** the spec, the parser, printer and verifier on both sides, and
  `fir-ref`. Until M4 the naive backend rejects inline assembly with a
  diagnostic. The C frontend brings constraint handling.

[semantics-m1-design.md](../decisions/semantics-m1-design.md) states each
rule. The human ruled this on 2026-11-09, on #220, and on 2026-11-11 on #251
(the effect set decides) and on #299 (the answer depends on the memory read).

## Why

The Linux kernel (M5) and the system headers of C and C++ (M4) need inline
assembly, and the spec cannot know what a block does. G0 forbids anything that
makes fir CPU-only, so the block names its target and the world answers it.
Keying an unobservable block on the memory it reads stops a pass from hoisting
a block that reads changing memory out of a loop.

## Rejected alternatives

- **The backend emits it in M1.** GCC constraint handling would join the IR
  milestone.
- **A reserved hook only, shaped in M4.** The format would not be settled when
  M1 claims the IR is complete.
- **Every block is an event.** Observable would mean nothing for a block, and
  passes could never remove one that only computes.
- **Key an unobservable block by the block and its operands only.** A block
  that reads changing memory would have to be marked observable, which is
  surprising and makes a common kind of block run worse.
