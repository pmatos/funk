# A module holds one abstraction level, a lowering must refine, and a dialect need not lower to core

Status: accepted
Tier: direction; area: semantics

## Decision

- **One level per module.** In v0 a module holds ops of one abstraction
  level, and lowering takes a whole module from one level to the next. Levels
  mix only through nested modules (ADR-2026-11-09-1543): a host module at one
  level may hold a device module at another.
- **Every lowering must refine.** A lowering that funk performs, from one
  dialect set to another, must produce a module that refines its input
  (ADR-2026-11-09-1540). It is proved once in Lean, or checked per compile
  once S8 exists.
- **Terminal dialects.** A dialect is not required to lower to core. A
  terminal dialect is lowered only by its own backend, to its own hardware.
  Its programs are still checked by its semantics in `fir-ref`, and its
  backend is checked against `fir-ref` like the x86-64 backend, by refinement
  of observed runs.

[semantics-m1-design.md](../decisions/semantics-m1-design.md) states each
rule. This is decision H5 of the fir v0 decision record. The human ruled it on
2026-11-09, on #202.

## Why

G0 (ADR-2026-10-29-2016) asks that fir reach any hardware. A quantum or
photonic dialect has no lowering to a CPU-shaped core, so it must be able to
stop at its own backend and still be checked. One level per module keeps each
lowering a whole-module step whose refinement can be stated once. M1's second
dialect is terminal (ADR-2026-11-09-1545), which tests this rule.

## Rejected alternatives

- **A closed core, with extensions admitted only with a verified lowering to
  core,** as the decision record proposed. Non-CPU dialects would have to
  pretend to be CPU code, against G0.
