# Current decisions: fir-ref, runs with memory

This page continues [fir-ref.md](fir-ref.md). It says how `fir-ref` runs a program with
memory. It is the record: when this page and an ADR disagree, the page wins, and
the ADR is fixed or deleted (ADR-2026-11-09-1610).

## The modes run with memory

`Core.scripted`, `Core.exhaustive` and `Core.sampled` walk `Func.memTree`: the
run in the state layer over the tree of choices, from the empty memories,
with the memories dropped at the end of each path. Each mode takes the unit
width of each memory first. `fir-ref` names the core's memories by
themselves, by their numbers, and `FirRef.coreUnit` gives each the unit of
its entry in the module's data layout (ADR-2026-11-12-1821). A memory that
the layout does not declare gets the unit of `MemLayout.default`, 8 bits.
Validation rejects every pointer type that names such a memory, but
`fir-ref run` runs a module without validating it, so an invalid module may
reach one. No core op names a memory yet, so the widths change no run;
stage 4e of #231, which brings loads and stores, says what `fir-ref run`
does with an access to an undeclared memory. The core's semantics in the
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
memory; a run of the corpus takes the same. `Memories.mem` grows by one
closure per store, allocation or free, so stage 4 must give the memories a
representation whose lookups take no stack per update before `fir-ref` runs
memory ops.
