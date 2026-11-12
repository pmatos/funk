# Current decisions: semantics, what an M1 run shows

This page continues semantics-m1-design.md. It says what the ADRs decide about
what a run shows in M1 and how the world outside the module answers it. It is
the record: when this page and an ADR disagree, the page wins, and the ADR is
fixed or deleted (ADR-2026-11-09-1610). ADR-2026-11-09-1540 holds the
direction decision.

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
  (ADR-2026-11-09-1552). semantics-m1-design.md has the rule.

The trace ends in one of three ways (ADR-2026-11-09-1540):

- a return, with the returned values and the contents of the memory an observer
  sees;
- UB;
- divergence.

Two ends of a run match when some one-to-one renaming of allocations makes
their observed memory equal. Raw addresses are never compared. Memory that no
observer can reach stays invisible, so a store to it can be removed
(ADR-2026-11-09-1540).

Another dialect may add events of its own, such as a device's I/O, since
observations already come from the dialect (ADR-2026-11-09-1540).

S4 makes correctness the refinement of observable behaviour, and the human
ruled what a run shows on 2026-11-09, on #207. Rejected: calls and returned
values only, with no memory at the end of a run, so a wrong store to a global
would go unnoticed unless a call revealed it. Rejected too: all live memory at
the end of a run, which makes every store observable and forbids removing dead
stores and most memory optimizations.

## What an observer sees at a return

At a return, an observer sees the contents of (ADR-2026-11-09-1540):

- every `export` global;
- the memory reachable from them and from the returned pointers;
- the memory that escaped, and the memory reachable from it.

The human ruled this on 2026-11-11, on #251. Rejected: every global is
observable, so C's `static` data could never be optimized away.

An address escapes whenever an op hands it to code outside the program, as in
LLVM's capture tracking (ADR-2026-11-09-1540):

- an external call that gets it as an argument;
- an inline assembly block whose effect set says observable;
- a volatile store whose stored value is the pointer;
- `ptr.expose`.

An `internal` global is observable only once its address escapes by one of
these ways, even when only an integer from `ptr.expose` holds it. Until then a
store to it is invisible and can be removed, and a pass that removes one first
checks every way above. An `export` global is observed whether or not its
address escapes (ADR-2026-11-09-1540).

Only live allocations are compared. The contents of an allocation that the
world has freed are not (ADR-2026-11-09-1540).

The human ruled escape and live memory on 2026-11-11, on #299. Rejected: only
external calls let an address escape, so passes could delete writes to memory
that assembly or a volatile store had already handed out. Rejected too:
compare a freed allocation as it was just before the free, though no program
can read it without UB. #309 asks two questions that these rulings leave open,
and neither is decided.

## The world

A callee that funk did not compile answers from the world. For each call, the
world gives its results and may write into memory that has escaped to it.
Behaviour is stated for a given world. The world is not the environment of
values in which a run looks names up (ADR-2026-11-09-1540).

When the world answers an external call, it may also (ADR-2026-11-09-1540):

- create fresh allocations of kind heap, in a named memory;
- free heap allocations that have escaped to it;
- return pointers into the allocations it creates, or write such pointers into
  escaped memory.

A fresh allocation has escaped to the world from the start. Once an access
reaches a heap allocation that the world freed, it is UB, as for any freed
allocation. `malloc`, `free` and their kin stay ordinary external declarations,
and no op allocates on the heap (ADR-2026-11-09-1540, ADR-2026-11-09-1548).

The human ruled this on 2026-11-11, on #251. Rejected: heap ops in the core.
ADR-2026-11-09-1548 rejected them, and C code calls allocators that funk does
not know by name.

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
allocations as part of a call's answer. It answers an observable inline
assembly block in trace order, and one without observable by the block, its
operands and the contents of the memories it declares it reads
(ADR-2026-11-09-1540, ADR-2026-11-09-1552). A test that calls an external
function must come with its script. `fir-ref run` reports the trace and the end
of the run (ADR-2026-11-09-1540).

For a native run, the harness generates a stub library from the same script. It
is linked in place of the external functions. It records each call (symbol,
arguments, reachable bytes), replays the scripted results and tracks the
script's frees. A wrapper that the harness generates dumps the live observed
memory at return: `export` globals, returned pointers and memory that escaped by
any of the ways above. The one judgement module compares the two sides
(ADR-2026-11-09-1540,
[testing-and-harness.md](testing-and-harness.md#where-the-judgement-lives)).
