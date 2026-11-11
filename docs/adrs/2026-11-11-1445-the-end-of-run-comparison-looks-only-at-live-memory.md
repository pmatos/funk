# The end-of-run comparison looks only at live memory, so allocations the world freed are not compared

Status: accepted
Tier: direction; area: semantics

## Context

ADR-2026-11-11-1017 lets the world free heap allocations that have escaped to
it when it answers an external call. ADR-2026-11-11-1016 has an observer
compare escaped memory when a run returns. Neither says what happens to an
escaped allocation that the world has freed: that memory no longer exists.
The review of PR #298 raised this
([#299](https://github.com/pmatos/funk/issues/299)). The human ruled on #299
on 2026-11-11
([comment](https://github.com/pmatos/funk/issues/299#issuecomment-6798799252)).

## Decision

- **Live memory only.** At a return, the observer compares only live
  allocations among the memory it sees. The contents of an allocation that
  the world has freed are not compared.

This refines ADR-2026-11-11-1016's list of what an observer sees and
ADR-2026-11-11-1017's freeing. It agrees with ADR-2026-11-11-1002, whose
refinement of memories does not compare the units of a freed block.

## Alternatives

- **Compare freed allocations as they were just before the free.** After a
  free no program can read that memory without UB, so its contents cannot
  change anything that is observable.

## Consequences

- The harness's stub library tracks the script's frees, so the wrapper dumps
  only live escaped memory.
- The trace ticket ([#233](https://github.com/pmatos/funk/issues/233)), the
  calls to C ticket ([#239](https://github.com/pmatos/funk/issues/239)) and
  the harness's memory judgement
  ([#213](https://github.com/pmatos/funk/issues/213)) build this rule.
