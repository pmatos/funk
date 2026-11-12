# A run shows a trace of events and the memory that escaped, and refinement holds for every world that answers it

Status: accepted
Tier: direction; area: semantics

## Decision

- **A trace of events.** A run shows an ordered trace of events: external
  calls, volatile accesses and observable inline assembly blocks
  (ADR-2026-11-09-1552). Another dialect may add events of its own.
- **How a run ends.** A return, UB or divergence. At a return an observer sees
  the returned values and the live memory of every `export` global, of what
  escaped and of what is reachable from them or from the returned pointers.
- **Escape.** An address escapes when an op hands it to code outside the
  program, as in LLVM's capture tracking. Until then an `internal` global is
  not observed, so a store to it can be removed.
- **Up to renaming.** Two ends of a run match when some one-to-one renaming of
  allocations makes their observed memory equal. Raw addresses are never
  compared.
- **The world.** A callee that funk did not compile answers from the world:
  its results, writes into escaped memory, and heap allocations it creates or
  frees. `malloc` stays an external declaration.
- **Refinement.** A target refines a source when, for every world, each trace
  it shows is one the source shows, with poison refined as today. UB in the
  source allows only a target that first shows the source's events.

[semantics-m1-trace.md](../decisions/semantics-m1-trace.md) states each rule:
what each event holds, the ways an address escapes, and how tests script the
world. The human ruled this on 2026-11-09, on #207, and on 2026-11-11 on #251
(what an observer sees, heap from the world) and on #299 (escape, live memory
only).

## Why

S4 makes correctness the refinement of observable behaviour (ADR-2026-10-29-2008).
`fir-ref` cannot run a function that funk did not compile, and a native run
cannot show fir's logical memory, so both sides need one model of what lies
outside the module. Escape keeps dead stores removable without hiding what
outside code can read.

## Rejected alternatives

- **Calls and returned values only.** A wrong store to a global would go
  unnoticed unless a call revealed it.
- **All live memory, or every global, at the end.** Every store would become
  observable, so no dead store, not even to C's `static` data, could go.
- **Only external calls let an address escape.** Passes could delete writes
  that assembly or a volatile store had already handed out.
- **Compare freed allocations as they were before the free.** No program can
  read them without UB.
- **Heap ops in the core.** C calls allocators that funk does not know by name.
