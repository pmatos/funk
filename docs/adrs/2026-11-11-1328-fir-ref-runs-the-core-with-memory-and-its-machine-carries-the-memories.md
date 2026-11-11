# fir-ref runs the core with memory, and its machine carries the memories

Status: accepted
Tier: implementation; area: fir-ref

## Context

ADR-2026-11-10-2350 makes memory a state layer over the way of computing,
and says that `fir-ref` walks the layer over the tree of choices (#231).
Until now `Core.scripted`, `Core.exhaustive` and `Core.sampled` ran the
interpreter in the tree of choices with no memory, and `FirRef.Machine`
(ADR-2026-11-04-2132) computed that tree. Stage 4 of #231 adds ops that
load, store and allocate, so the modes must run with memory before those
ops exist, and the machine must still take no stack per step, per level of
calls or per choice.

## Decision

- **The spec's modes walk the run with memory.** `Func.memTree`
  ([`lean/Fir/Execution/MemoryModes.lean`](../../lean/Fir/Execution/MemoryModes.lean))
  is the run in `StateT (Memories N unit) (ChoiceTree ε)` from
  `Memories.empty`, with the memories dropped at the end of each path. The
  three core modes walk it, and take the unit width of each memory,
  `unit`, as their first argument. `Core.exhaustive_memOutcomes`,
  `Core.scripted_memOutcomes` and `Core.sampled_memOutcomes` (and their
  `memStuck` siblings) state them against `Func.memRuns` at every naming.
  `Core.memTree_eq` proves that the tree of a core run with memory is the
  tree of its run with no memory, so the modes report what they reported
  before, path for path, and the old theorems against the run in the set
  monad keep their proofs.
- **Leaves carry no memories.** A mode reports how a path ends, so the
  tree drops the memories before the walk, and `fir-ref`'s reports, leaves
  and JSON are unchanged. Observations at the end of a run (#233) decide
  what a run shows of its memories.
- **The core's semantics in the layer over the tree lifts its rules in the
  tree**, as its semantics with memory lifts its rules in the set monad
  (`DialectMemDenote.ofSetM`). `Core.memMapsDenote` ties the two at every
  naming. Stage 4 replaces both when core ops touch memory.
- **The machine carries the memories.** `Cur.ops` and `Cur.ret` hold the
  memories, and an op's or terminator's tree holds the memories after each
  of its paths. The machine enters a frame (`Memories.enter`) where it
  starts a callee, and the function a run starts with, and leaves it
  (`Memories.exit`) where the callee returns, as `inFrame` does. A path that
  ends drops its memories, so the machine never leaves the frames of the
  callers that wait. `FirRef.Steps` now holds for any lawful monad, and
  `ChoiceTree` is a lawful monad.
- **fir-ref names the core's memories by themselves.** `FirRef.coreUnit`
  gives each core memory its unit width. The core has no memory yet, so
  it is the empty function; the module's data layout gives the widths
  when it lands (#231).

## Consequences

- Stage 4's memory ops run in `fir-ref` once the core's semantics in the
  layer over the tree gives them their rules, with no change to the
  machine, `Func.memTree` or the statements of the `*_memOutcomes` and
  `*_memStuck` theorems. Stage 4 proves `Core.memMapsDenote` again for the
  new rules. `Core.memTree_eq` and the theorems against the run in the
  set monad hold only while no core op touches memory, so stage 4 restates
  or drops them.
- `Memories.mem` is a function, and each store, allocation or free wraps
  it in one more closure. Today the core touches no memory and a frame
  frees nothing, so the chain never grows. Once stage 4 allocates on the
  stack, a long run would build a long chain, and a lookup would walk it.
  Stage 4 must give the memories a representation whose lookups take no
  stack per update before `fir-ref` runs memory ops.
- Each op now runs through the layer's `bind`, so `fir-ref run` takes
  about 25 to 35% more time on a run of a million steps. On the corpus,
  where a run is short, the time is the same.
- `Memories` keeps a stack of frames beside the machine's own, so a deep
  recursion costs two lists on the heap, still no stack.
