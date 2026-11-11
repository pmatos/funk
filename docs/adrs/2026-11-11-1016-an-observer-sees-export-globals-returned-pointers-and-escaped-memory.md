# At the end of a run an observer sees export globals, returned pointers and escaped memory, and an internal global only once its address escapes

Status: accepted; refined by ADR-2026-11-11-1444 and
ADR-2026-11-11-1445
Tier: direction; area: semantics

## Context

ADR-2026-11-09-1540 ends a returning run with the contents of the memory
reachable from globals and from returned pointers. It does not say which
globals. ADR-2026-11-09-1546 names only `export` globals as reachable memory
for an observer. If every global counted, a store to an `internal` global
could never be removed, though no code outside the module can read it
([#251](https://github.com/pmatos/funk/issues/251)). The human ruled on #251
on 2026-11-11.

## Decision

- **What an observer sees.** When a run returns, an observer sees the
  contents of:
  - every `export` global;
  - the memory reachable from them and from the returned pointers;
  - the memory that escaped to an external call, and the memory reachable
    from it.
- **Internal globals.** An `internal` global is observable only once its
  address escapes: once it is reachable from what the observer sees.
  Until then a store to it is invisible and can be removed.

This tightens ADR-2026-11-09-1540's "reachable from globals", and gives
ADR-2026-11-09-1546's linkage rule its meaning at the end of a run.
Memory is still compared up to a renaming of allocations
(ADR-2026-11-09-1540).

## Alternatives

- **Every global is observable.** C's `static` data could never be
  optimized away, and every store to it would have to stay.

## Consequences

- Passes may remove dead stores to an `internal` global whose address never
  escapes.
- The harness's wrapper dumps `export` globals, returned pointers and escaped
  memory at return, and the judgement module compares only those
  ([#213](https://github.com/pmatos/funk/issues/213),
  [#233](https://github.com/pmatos/funk/issues/233)).
