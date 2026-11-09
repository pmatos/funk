# Inline assembly is an op tagged with its target, and running it is an event answered by the world

Status: accepted
Tier: direction; area: semantics

## Context

The Linux kernel (M5) cannot be built without inline assembly, and C and
C++ frontends (M4) meet it in system headers. The spec cannot know what an
assembly block does. G0 (ADR-2026-10-29-2016) forbids anything that makes
fir CPU-only. GCC-compatible constraint handling in a backend is a large
piece of C-compatibility work. The human ruled on
[#220](https://github.com/pmatos/funk/issues/220) on 2026-11-09.

## Decision

- **Shape.** An op tagged with its target, holding a template, constraints,
  operands, results, clobbers, and an explicit effect set
  (ADR-2026-11-09-1541), observable or not. A module for another target
  rejects it.
- **Semantics.** Running an assembly block is an event of the trace
  (ADR-2026-11-09-1540). The world answers it with its results and with
  writes into memory that its declared effects allow. `fir-ref` takes the
  answer from the test's script, as for external calls.
- **In M1:** the spec, formal and readable; the parser, printer and
  verifier on both sides; and `fir-ref`.
- **Until M4,** the naive backend rejects inline assembly with a
  diagnostic. The C frontend brings constraint handling.

## Alternatives

- **The backend emits it in M1 too.** It would pull GCC constraint handling
  into the IR milestone.
- **A reserved hook only, shaped in M4.** The format would not be settled
  when M1 claims the IR is complete.

## Consequences

- fir can hold kernel and system-header code from M1 on.
- Native runs of such code wait for M4.
