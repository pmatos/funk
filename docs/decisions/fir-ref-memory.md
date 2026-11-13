# Current decisions: fir-ref, runs with memory

This page continues [fir-ref.md](fir-ref.md). It says how `fir-ref` runs a program with
memory. It is the record: when this page and an ADR disagree, the page wins, and
the ADR is fixed or deleted (ADR-2026-11-09-1610).

## The modes run with memory

`Core.scripted`, `Core.exhaustive` and `Core.sampled` walk `Func.memTree`: the
run in the state layer over the tree of choices, from the empty memories,
with the memories dropped at the end of each path. Each mode takes the unit
width of each memory first. `fir-ref` names the core's memories by themselves,
and `FirRef.coreUnit` gives their widths; no core op names a memory yet, so
it is the empty function until stage 4 of #231 gives the core's memories
the widths of the module's data layout (ADR-2026-11-12-1821). The core's semantics in the
layer over the tree lifts its rules in the tree, as its semantics with memory
lifts its rules in the set monad (`DialectMemDenote.ofSetM`), and
`Core.memMapsDenote` ties the two at every naming.

`Core.exhaustive_memOutcomes`, `Core.scripted_memOutcomes` and
`Core.sampled_memOutcomes`, with their `memStuck` siblings, prove the modes
against `Func.memRuns` at every naming of the core's memories.
`Core.memTree_eq` proves that the tree of a core run with memory is the tree of
its run with no memory, so the modes report what they did before, path for
path, and `Core.exhaustive_outcomes` and its siblings keep their proofs. That
holds only while no core op touches memory. Reports, leaves and JSON are
those of runs without memory: a path shows how it ends and not its memories,
until observations at the end of a run are designed (#233). Stage 4 of #231
proves `Core.memMapsDenote` again for its memory ops, and restates or drops
`Core.memTree_eq` and the theorems against the run in the set monad.

## The machine carries the memories

`FirRef.Machine`'s states hold the memories: the ops of a block start from
given memories, an op's tree gives the memories after each of its paths, and
a function returns with its memories. The machine enters a frame where it
starts a callee and the function a run starts with, and leaves it where the
callee returns, as the interpreter's frame does. `Machine.advance_tree`
proves that it computes the spec's tree of the run with memory, so the
`@[csimp]` theorems of `FirRef.Run` hold as before
([Running](fir-ref-fast-paths.md#running)). `FirRef.Steps` holds for any lawful
monad, and the tree of choices is a lawful monad. A path that ends drops its
memories, so the machine never leaves the frames of the callers that wait.
`Memories` keeps a stack of frames beside the machine's own, so a deep
recursion costs two lists on the heap, still no stack.

The machine still takes no stack per step, per level of calls or per
choice. A run of a million steps takes about a third more time than without
memory; a run of the corpus takes the same.

## The memories are a table

`Memories` keeps its memories in a table: a list of memories, each with its
name (`lean/Fir/Memory/Frames.lean`). `Memories.mem x` is the first memory
named `x` in the table, or the empty memory when the table has none, and
`Memories.set` puts the new memory first and drops every older entry of its
name. So the table holds each name at most once, however many stores,
allocations and frees a run makes, and it grows only when a memory that the
run has not touched before changes. A lookup is a tail-recursive walk of at
most as many entries as the run has memories, and `set` filters the table
with `List.filter`, which runs as `List.filterTR`; the C that Lean emits
for `Memories.lookup` is a loop. So a lookup takes no stack per update, and
`fir-ref` may run memory ops (stage 4c of #231). This is the spec's own
definition, not a fast path: `fir-ref` runs it as written, and the
`@[csimp]` theorems of the machine, which hold for any state, are unchanged.
`set_mem_self` and `set_mem_ne` give the memories after a replacement, with
no axiom, and the laws of the memories reach the table only through them, so
each law holds as before.

Rejected: keep `mem` a function of the names and replace it with a closure
per update. Each lookup then walks every update made since the run began,
one call per closure, so it takes stack and time in proportion to the
stores, allocations and frees before it.
