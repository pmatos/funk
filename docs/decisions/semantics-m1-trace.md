# Current decisions: semantics, what an M1 run shows

This page continues semantics-m1-design.md. It says what the ADRs decide about
what a run shows in M1 and how the world outside the module answers it. It
summarizes the ADRs it cites and does not replace them. When this page and an
ADR disagree, the page is wrong (ADR-2026-11-09-1610).

These are decided designs, and the spec and the tools do not implement them
yet. semantics.md says what a run shows in M0.

## What a run shows

A run shows an ordered trace of events (ADR-2026-11-09-1540). The core dialect
has these kinds of event:

- An external call: the callee's symbol, its arguments, and the units reachable
  from its pointer arguments when the call is made.
- A volatile access: load or store, the accessed location as the observer sees
  it, and the value read or written.
- An inline assembly block whose effect set says observable
  (ADR-2026-11-11-1015). semantics-m1-design.md has the rule.

The trace ends in one of three ways (ADR-2026-11-09-1540):

- a return, with the returned values and the contents of the memory an observer
  sees;
- UB;
- divergence.

At a return, an observer sees the contents of (ADR-2026-11-11-1016):

- every `export` global;
- the memory reachable from them and from the returned pointers;
- the memory that escaped to an external call, and the memory reachable from it.

An `internal` global is observable only once its address escapes: once it is
reachable from what the observer sees. Until then a store to it is invisible
and can be removed (ADR-2026-11-11-1016).

Two ends of a run match when some one-to-one renaming of allocations makes
their observed memory equal. Raw addresses are never compared. Memory that no
observer can reach stays invisible, so a store to it can be removed
(ADR-2026-11-09-1540).

Another dialect may add events of its own, such as a device's I/O, since
observations already come from the dialect (ADR-2026-11-09-1540).

## The world

A callee that funk did not compile answers from the world. For each call, the
world gives its results and may write into memory that has escaped to it.
Behaviour is stated for a given world. The world is not the environment of
values in which a run looks names up (ADR-2026-11-09-1540).

When the world answers an external call, it may also (ADR-2026-11-11-1017):

- create fresh allocations of kind heap, in a named memory;
- free heap allocations that have escaped to it;
- return pointers into the allocations it creates, or write such pointers into
  escaped memory.

A fresh allocation has escaped to the world from the start. `malloc`, `free`
and their kin stay ordinary external declarations, and no op allocates on the
heap (ADR-2026-11-11-1017, ADR-2026-11-09-1548).

## Refinement

A target refines a source when it does so for every world. For each world,
every trace the target shows is one the source shows, with poison refined as
today. UB in the source allows only a target that first shows the source's
events before the UB (ADR-2026-11-09-1540).

Every refinement theorem gains a quantifier over worlds. The first theorems to
be restated are those that #206 and #209 touch.

## Scripts and native runs

Each test supplies a scripted world: the results of each external call, in
order, and any writes into escaped memory. The script may create and free heap
allocations as part of a call's answer (ADR-2026-11-11-1017). It answers an
observable inline assembly block in trace order, and one without observable by
the block and its operands (ADR-2026-11-11-1015). A test that calls an external
function must come with its script. `fir-ref run` reports the trace and the end
of the run (ADR-2026-11-09-1540).

For a native run, the harness generates a stub library from the same script. It
is linked in place of the external functions. It records each call (symbol,
arguments, reachable bytes) and replays the scripted results. A wrapper that the
harness generates dumps the observed memory at return. The one judgement module
compares the two sides (ADR-2026-11-06-1218, ADR-2026-11-09-1540).
