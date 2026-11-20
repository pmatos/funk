# Current decisions: semantics, what an M1 run shows

This page continues semantics-m1-design.md. It says what the ADRs decide about
what a run shows in M1 and how the world outside the module answers it. It is
the record: when this page and an ADR disagree, the page wins, and the ADR is
fixed or deleted (ADR-2026-11-09-1610). ADR-2026-11-09-1540 holds the
direction decision.

These are decided designs. The spec defines traces, worlds and traced
refinement (`lean/Fir/Execution/Trace*.lean`), and what an observer sees at
a return and the world's actions on escaped memory
(`lean/Fir/Execution/Observe*.lean`, `TraceWorld.lean`), and the core's and
CoreGpu's traced runs, with refined arguments and congruence in the callee
over them while they show no event (`lean/Fir/Execution/TraceLift.lean`,
`TraceRefine.lean`, `lean/Fir/Core/Trace.lean`, `lean/Fir/Gpu/Trace.lean`).
Refinement over traces for a dialect that shows events, and `fir-ref`'s
scripted worlds, are not implemented yet (#233, stages 3b, 3c and 4).
semantics-refinement.md says what a run shows in M0.

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
- an inline assembly block that gets it as a pointer operand and may write
  escaped memory, when the block runs (ADR-2026-11-09-1541);
- a volatile store whose stored value is the pointer;
- `ptr.expose`.

A block without a narrower declaration may write escaped memory, so its
pointer operands escape. A pointer passed to an inline assembly block that is
not observable and may not write escaped memory does not escape, though the
block may read and write the allocation it points into and every allocation
reachable from it through stored pointers (ADR-2026-11-09-1541,
semantics-effects.md). The human ruled this escape rule on 2026-11-15, on #240.
Rejected: only observable blocks make memory escape, though such a block could
store its operand in escaped memory, where outside code could read it.

An `internal` global is observable only once its address escapes by one of
these ways, even when only an integer from `ptr.expose` holds it. Until then a
store to it is invisible and can be removed, and a pass that removes one first
checks every way above. An `export` global is observed whether or not its
address escapes (ADR-2026-11-09-1540).

Only live allocations are compared. The contents of an allocation that the
world has freed are not (ADR-2026-11-09-1540).

A run can still hold a pointer into a freed allocation, one the world freed or
a stack allocation whose call has returned, and the renaming has nothing to map
it to. In the comparison of two runs, such a pointer is poison wherever the
source has it: in observed memory, in returned values and in the arguments of
an external call, an event of the trace. Any value in the target refines it
(ADR-2026-11-09-1540). A dangling pointer cannot be used without UB, so nothing
a program does can depend on its value.

The human ruled escape and live memory on 2026-11-11, on #299. Rejected: only
external calls let an address escape, so passes could delete writes to memory
that assembly or a volatile store had already handed out. Rejected too:
compare a freed allocation as it was just before the free, though no program
can read it without UB.

The human ruled on 2026-11-15 (#309), option C, that a dangling pointer in
observed memory is poison for the comparison. Rejected: every dangling pointer
equals every other, which still makes a target keep a dangling pointer wherever
the source has one. Rejected too: compare a dangling pointer by its integer
address where the memory is integral, and otherwise as dangling, which compares
raw addresses that the renaming exists to avoid. On 2026-11-15 the human ruled
on #233 that a dangling pointer is poison in returned values and external-call
arguments too. Rejected: exact match outside observed memory, so a target would
keep a dangling pointer in a return or a call that neither side can use without
UB.

## How the spec states the end of a return

These are #233's choices of form, within the rules above.

- **Handles.** The world never sees an allocation id. A traced run keeps
  the list of the allocations that escaped, in the order they escaped, and
  the world names each by its place in that list, its handle
  (`TraceState`). Source and target answered at the same world then get
  the same answers, by handle, though their ids differ. Rejected: answers
  that name allocation ids, compared up to a renaming of the whole trace,
  under which the world could tell source and target apart by an id.
- **Who escapes what.** The layer gives the escape effect; the op that
  hands out an address escapes each allocation it reaches, so an external
  call (#239) escapes the closure of its pointer arguments and of the
  allocations already escaped when it is made, since a pointer stored into
  escaped memory is handed out too, as in LLVM's capture tracking.
  It escapes them in an order fixed by the arguments and by where each
  pointer is stored, never by allocation ids, so that source and target
  give the same allocations the same handles. Only a live allocation can
  escape: a dangling pointer is poison in the comparison, so it escapes
  nothing. The world's heap allocations are aligned to a power of
  two, as every allocation is (#231).
  The `export` globals (#237) and `ptr.expose` (#232) join the roots when
  they exist.
- **The renaming.** One-to-one, partial, and closed under the live
  pointers of the allocations it relates, driven from the source's side
  (`End.SeenUnder`): it renames each allocation that the observer reaches
  (`End.SeenUnder.reachable`), and no other needs comparing. The escaped
  allocations keep their handles, so the renaming is fixed on them. An id
  that the source never allocated is renamed to one the target never
  allocated. Each fragment of a pointer holds the whole pointer, so a
  single fragment in observed memory makes its allocation reachable.
- **Where the world acts.** `TraceM.ask` applies the world's actions: a
  write inside an escaped live allocation, a heap allocation that escapes
  at once, and a free of an escaped live heap allocation. The act records
  them beside the result.
- **Addresses.** The end of a return does not compare the numeric
  addresses of the allocations it relates: an address is seen only through
  the integers a run shows, as raw addresses are never compared
  (ADR-2026-11-09-1540). The spec's end of a return and traced runs fix the
  rule `AddrRule.ignore` (`ObservedEnd`, `Func.observedRuns`); the
  comparison still takes an address rule, and every law holds for each of
  `ignore`, `same` and `exposed`. The human ruled this on 2026-11-20, on
  #233. Rejected: `AddrRule.same`, under which related allocations keep the
  same address, which forbids a pass to move an exposed allocation.

When the source returns no pointer and nothing escaped, the end of its
return is refined exactly when its returned values are and nothing escaped
in the target (`End.isRefinedBy_iff_vals`), so M0's tests keep their
results.

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

The world answers what the target shows: poison inside an event is refined
by any value (ADR-2026-11-09-1540). The human ruled this on 2026-11-18, on
#233, option A. In the spec, the world's answer to an event is any answer, and the trace
records it. One act refines another when its event refines the other's, with
poison refined as for values, and both have the same answer, so the world
answers what the target shows: where the source shows poison in an event, the
target may show any value, and the world's answer to that value is an answer
to the source's poison, which may be any value. Refinement of traced
behaviours is then equivalent to refinement at every world, since every trace
is shown at some world. Rejected (option B): a world that answers the
source's poison and the target's value apart. Refined arguments would then fail: a function
that returns the world's answer to its argument would return different values
on poison and on 5 at a world that answers them differently.

A traced run diverges in one of two ways: it falls silent after a finite
trace, or it shows acts forever. Neither refines the other, and a run that
shows one act and then falls silent refines neither. Each op that runs by
its dialect's rule marks a step in the trace, which the world never sees (a
call marks none of its own; its callee's ops mark theirs), so divergence is
judged by when a run showed its acts: a run that may return arbitrarily late after its last act
does not fall silent after it, and a run that may show arbitrarily many acts
before it returns does not show acts forever. Rejected: judge divergence only
by the acts that a run has shown when it runs out of fuel at each budget,
which cannot tell those runs from runs that hang after the acts, or show
acts forever. A run with no event is a
traced run whose every trace is empty, and its traced refinement is its
refinement as today. M0's dialects show no event, so once they run in the
traced layer their tests keep their results.

## Refinement over traced runs

These are #233's choices of form for its third stage, within the rules
above.

- **A dialect with no event.** Its traced semantics is its semantics with
  memory, lifted onto the memories of the traced state
  (`DialectTrace.ofMem`), so it lifts it (`LiftsMem`) by construction. The
  core and CoreGpu have this traced semantics until their events exist.
  Rejected: a traced semantics written op by op for the core now, which
  #239 would rewrite once the core shows its first event.
- **From memory to the end of a return.** Returned values that refine
  others and memories that refine others, with the same allocations
  escaped, give ends of returns that refine each other under the renaming
  of every allocation to itself (`End.isRefinedBy_of_mem`). So, for a
  dialect with no event, refinement from the empty memories, the memories
  each run ends with included, gives refinement of its traced runs
  (`Func.traceRuns_isRefinedBy_of_from`), and refined arguments and
  congruence in the callee from given memories hold over its traced runs
  and at every world (`Fir.Execution.TraceRefine`). The core and CoreGpu
  state both over the spec's traced runs (`Func.observedRuns`), with no
  hypothesis beyond those they have with memory.
- **A dialect with events.** Its refined arguments and congruence in the
  callee need the traced layer's own theorems (#233, stages 3b and 3c),
  which prove the core's statements again, unchanged, once the core shows
  events. Divergence there needs one source trace at every budget: an op
  with infinitely many outcomes `c` can show, on a poison argument, an
  event that differs with each `c` and is refined by the target's, then
  take `c` silent steps and return. The target then falls silent after its
  event, and no source outcome allows it. So those theorems are to ask
  that each op have finitely many outcomes, given the world's answers, as
  congruence with memory asks with `OpsFinite`; the core and CoreGpu meet
  this.

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
