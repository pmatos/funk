# The second dialect in tree is GPU-kernel-shaped, and M1 runs one work-item of a kernel at a time

Status: accepted
Tier: direction; area: semantics

## Context

M1 is done when the G0 checks pass with a second dialect in tree, so that
G0's openness (ADR-2026-10-29-2016) is tested and not only promised. Today
`funk` and `fir-ref` are fixed to the core dialect, and the only other
dialects are test-only. A CPU-shaped second dialect would pass the checks
without testing the openness they are meant to show. Concurrency (S6) is
out of M1. The human ruled on
[#202](https://github.com/pmatos/funk/issues/202) on 2026-11-09.

## Decision

- **Shape.** The second dialect is shaped like a GPU kernel language:
  - A host module holds a nested device module (ADR-2026-11-09-1543) whose
    dialect set includes the GPU dialect. Kernel functions live in the
    device module.
  - It adds ops of its own, such as work-item and work-group ids and sizes,
    and at least one type or attribute of its own.
  - It adds a memory in a non-default address space, such as work-group
    shared memory (ADR-2026-11-09-1542), with effects named by that memory
    (ADR-2026-11-09-1541).
- **One work-item in M1.** `fir-ref` runs one work-item of a kernel, with
  its ids given as inputs. Ops whose meaning needs other work-items, such
  as barriers, are left out or admitted without execution rules
  ([fir-ref.md](../decisions/fir-ref.md#an-op-without-rules)). A launch op in
  host code is out of M1. M1's results are not a model of a whole kernel.
- **Terminal.** The dialect has no lowering to core and no native backend
  in M1 (ADR-2026-11-09-1544).
- **What the G0 checks show with it.**
  - Generic code in `funk-ir` and `lean/Fir` loads it with no change but
    its registration.
  - A host module with a device module round-trips byte for byte across
    Rust and Lean, and both sides validate it the same way, must-reject
    cases included.
  - Its kernels run in `fir-ref` one work-item at a time, and `funk` and
    `fir-ref` agree on its corpus.
  - The generic results (round trip, refinement, congruence) are restated
    for a dialect set that includes it.
- Use-once (linear) values stay covered by the toy test of
  [#167](https://github.com/pmatos/funk/issues/167). A quantum-style
  dialect remains a candidate for a later G0 check.

## Alternatives

- **A small quantum-style dialect** with a qubit type, a use-once rule and
  measurement as a choice. It is less CPU-shaped and runs fully under set
  semantics, but tests neither nested modules nor several memories.
- **A CPU-shaped dialect,** such as checked arithmetic. It is cheapest but
  tests little of what G0 is about.

## Consequences

- M1 exercises nested modules, several memories, dialect sets and terminal
  dialects together.
- The dialect's semantics grows into a full kernel model only when S6
  decides concurrency.
- Its implementation ([#212](https://github.com/pmatos/funk/issues/212))
  waits for memory and for nested modules.
