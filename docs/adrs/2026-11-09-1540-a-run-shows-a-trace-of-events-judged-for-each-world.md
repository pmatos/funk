# A run shows a trace of external calls and volatile accesses, and refinement holds for every world that answers them

Status: accepted; refined by ADR-2026-11-11-1016 and ADR-2026-11-11-1017
Tier: direction; area: semantics

## Context

S4 (ADR-2026-10-29-2008) defines correctness as refinement of observable
behaviour. In M0 a run shows only how it ends: the values it returns, UB,
or running out of fuel. ADR-2026-10-29-2008 says the full definition also
counts calls to external symbols and reachable memory, and that the
relation stays the same when they arrive. M1 brings both: memory
([#206](https://github.com/pmatos/funk/issues/206)) and external
declarations ([#209](https://github.com/pmatos/funk/issues/209)).

`fir-ref` cannot run a function that funk did not compile, and a native run
cannot show fir's logical memory. Both sides need one model of what lies
outside the module. The human ruled on
[#207](https://github.com/pmatos/funk/issues/207) on 2026-11-09.

## Decision

- **A trace of events.** A run shows an ordered trace of events:
  - an **external call**: the callee's symbol, its arguments, and the
    units reachable from its pointer arguments when the call is made;
  - a **volatile access** (ADR-2026-11-09-1548): load or store, the
    accessed location as the observer sees it, and the value read or
    written.
- **How a run ends.** The trace ends in one of three ways:
  - a return, with the returned values and the contents of the memory
    reachable from globals and from returned pointers;
  - UB;
  - divergence.
- **Memory is compared up to renaming.** Two ends of a run match when some
  one-to-one renaming of allocations makes their reachable memory equal.
  Raw addresses are never compared. Memory that no observer can reach
  stays invisible, so a store to it can be removed.
- **The world.** A callee that funk did not compile answers from the
  *world*: for each call, the world gives its results and may write into
  memory that has escaped to it. Behaviour is stated for a given world, and
  a target refines a source when it does so for every world. The word
  "world" keeps this apart from the environment of values that a run looks
  names up in
  ([`Environment.lean`](../../lean/Fir/Execution/Environment.lean)).
- **Refinement.** For each world, every trace the target shows is one the
  source shows, with poison refined as today. UB in the source allows only
  a target that first shows the source's events before the UB.
- **`fir-ref`.** Each test supplies a scripted world: the results of each
  external call, in order, and any writes into escaped memory. `fir-ref
  run` reports the trace and the end of the run.
- **Native runs.** The harness generates a stub library from the same
  script. It is linked in place of the external functions. It records each
  call (symbol, arguments, reachable bytes) and replays the scripted
  results. A wrapper that the harness generates dumps the reachable memory
  at return. The harness's single judgement module
  ([testing-and-harness.md](../decisions/testing-and-harness.md#where-the-judgement-lives))
  compares the two sides ([#213](https://github.com/pmatos/funk/issues/213)).
- **Dialects add events.** The events above are the core dialect's. Another
  dialect may add events of its own, such as a device's I/O, since
  observations already come from the dialect (G0, ADR-2026-10-29-2016).

## Alternatives

- **Calls and returned values only, with no memory at the end of a run.**
  A wrong store to a global would go unnoticed unless a call revealed it.
- **All live memory at the end of a run.** Every store would become
  observable, which forbids removing dead stores and most memory
  optimizations.

## Consequences

- The harness can catch a wrong store and a wrong external call, not only a
  wrong returned value.
- A test that calls an external function must come with its script. A test
  whose observations depend on an exposed address is interpreter-only
  (ADR-2026-11-09-1542).
- Every refinement theorem gains a quantifier over worlds. The first
  theorems to be restated are those that #206 and #209 touch.
