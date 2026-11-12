# The second dialect in tree is GPU-kernel-shaped, and M1 runs one work-item of a kernel at a time

Status: accepted
Tier: direction; area: semantics

## Decision

- **Shape.** The second dialect is shaped like a GPU kernel language. A host
  module holds a nested device module (ADR-2026-11-09-1543) whose dialect set
  includes the GPU dialect, and kernel functions live there. It adds ops of
  its own, such as work-item and work-group ids and sizes, at least one type
  or attribute of its own, and a memory in a non-default address space, such
  as work-group shared memory (ADR-2026-11-09-1542), with effects named by
  that memory.
- **One work-item in M1.** `fir-ref` runs one work-item of a kernel, with its
  ids given as inputs. Ops whose meaning needs other work-items, such as
  barriers, are left out or admitted without execution rules. A launch op in
  host code is out of M1, and M1's results are not a model of a whole kernel.
- **Terminal.** It has no lowering to core and no native backend in M1
  (ADR-2026-11-09-1544).
- **What the G0 checks show with it.** Generic code in `funk-ir` and
  `lean/Fir` loads it with no change but its registration. A host module with
  a device module round-trips byte for byte across Rust and Lean, and both
  sides validate it alike, must-reject cases included. Its kernels run in
  `fir-ref` one work-item at a time, and `funk` and `fir-ref` agree on its
  corpus. The generic results are restated for a dialect set that includes
  it.

[semantics-m1-design.md](../decisions/semantics-m1-design.md) states each
rule. The human ruled this on 2026-11-09, on #202.

## Why

M1 is done when the G0 checks pass with a second dialect in tree, so that
G0's openness (ADR-2026-10-29-2016) is tested, not only promised. A GPU-shaped
dialect exercises nested modules, several memories, dialect sets and terminal
dialects together. Concurrency (S6) is out of M1, so one work-item is what M1
can model; the semantics grows into a whole kernel when S6 decides
concurrency.

## Rejected alternatives

- **A small quantum-style dialect,** with a qubit type, a use-once rule and
  measurement as a choice. It tests neither nested modules nor several
  memories. It stays a candidate for a later G0 check.
- **A CPU-shaped dialect,** such as checked arithmetic. Cheapest, but it tests
  little of what G0 is about.
