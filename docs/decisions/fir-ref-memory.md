# Current decisions: fir-ref, runs with memory

This page continues fir-ref.md. It says how `fir-ref` runs a program with
memory. It summarizes the ADRs it cites and does not replace them. When this
page and an ADR disagree, the page is wrong (ADR-2026-11-09-1610).

## The modes run with memory

`Core.scripted`, `Core.exhaustive` and `Core.sampled` walk `Func.memTree`: the
run in the state layer over the tree of choices, from the empty memories,
with the memories dropped at the end of each path. Each mode takes the unit
width of each memory first. `fir-ref` names the core's memories by themselves,
and `FirRef.coreUnit` gives their widths; the core has no memory yet, so it
is the empty function until the data layout lands (ADR-2026-11-11-1328).

`Core.exhaustive_memOutcomes`, `Core.scripted_memOutcomes` and
`Core.sampled_memOutcomes`, with their `memStuck` siblings, prove the modes
against `Func.memRuns` at every naming of the core's memories. The core's runs
with memory are its runs, so the theorems against the run in the set monad,
such as `Core.exhaustive_outcomes`, still hold. Reports, leaves and JSON are
those of runs without memory: a path shows how it ends and not its memories,
until observations at the end of a run are designed (#233,
ADR-2026-11-11-1328).

## The machine carries the memories

`FirRef.Machine`'s states hold the memories: the ops of a block start from
given memories, an op's tree gives the memories after each of its paths, and
a function returns with its memories. The machine enters a frame where it
starts a callee and the function a run starts with, and leaves it where the
callee returns, as the interpreter's frame does. `Machine.advance_tree`
proves that it computes the spec's tree of the run with memory, so the
`@[csimp]` theorems of `FirRef.Run` hold as before. `FirRef.Steps` holds
for any lawful monad, and the tree of choices is a lawful monad
(ADR-2026-11-04-2132, ADR-2026-11-11-1328).

The machine still takes no stack per step, per level of calls or per
choice. A run of a million steps takes about a third more time than without
memory; a run of the corpus takes the same (ADR-2026-11-11-1328).
