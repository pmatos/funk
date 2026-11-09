# A module holds one abstraction level, a lowering must refine, and a dialect need not lower to core

Status: accepted
Tier: direction; area: semantics

## Context

This is decision H5 of the fir v0 decision record. The record proposed one
abstraction level per module in v0, with lowering a whole module at a time.
It also proposed a closed core with extensions admitted only with a
verified lowering to core. G0 (ADR-2026-10-29-2016) came after that
proposal: a dialect for quantum or photonic hardware has no lowering to a
CPU-shaped core. The human ruled on
[#202](https://github.com/pmatos/funk/issues/202) on 2026-11-09.

## Decision

- **One level per module.** In v0 a module holds ops of one abstraction
  level, and lowering takes a whole module from one level to the next.
  Levels mix only through nested modules (ADR-2026-11-09-1543): a host
  module at one level may hold a device module at another.
- **Every lowering must refine.** A lowering that funk performs, from one
  dialect set to another, must produce a module that refines its input
  (ADR-2026-11-09-1540). It is proved once in Lean, or checked per compile
  once S8 exists.
- **Terminal dialects.** A dialect is not required to lower to core. A
  *terminal* dialect is lowered only by its own backend, to its own
  hardware. Its programs are still checked by its semantics in `fir-ref`.
- This replaces the record's "extensions only with a verified lowering to
  core".

## Consequences

- Quantum, photonic and other non-CPU dialects fit fir without pretending
  to be CPU code.
- A terminal dialect's backend is checked against `fir-ref` like the
  x86-64 backend, by refinement of observed runs.
- M1's second dialect is terminal (ADR-2026-11-09-1545), which tests this
  rule.
