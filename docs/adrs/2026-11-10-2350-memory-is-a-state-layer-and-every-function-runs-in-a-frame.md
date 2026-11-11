# Memory is a state layer over the way of computing, and every function runs in a frame

Status: accepted
Tier: direction; area: semantics

## Context

ADR-2026-11-09-1542 makes memory logical blocks in typed memories, and
ADR-2026-11-09-1548 frees a stack allocation when the call that made it
returns. The spec's interpreter is written once for any monad, and each
dialect states the effects its ops need as classes on that monad
(ADR-2026-10-29-2030). M0's runs, `fir-ref`'s modes and every proof about
runs use the set monad or the tree of choices, which have no memory. Memory
had to become part of a run without a second interpreter, and the
interpreter had to free a call's stack allocations without knowing what
memory is (G0, ADR-2026-10-29-2016).

## Decision

- **The memories of a run are one state.** `Memories Mem unit` in
  `lean/Fir/Memory/Frames.lean` holds one memory of the model for each
  memory name, with a unit width per name that the data layout will give,
  and a stack of frames. A frame lists the stack allocations its call made.
- **Memory is an effect.** `MonadMemory` gives allocating, freeing, loading
  and storing, each on a named memory; a faulting access is UB.
- **The interpreter runs every function in a frame.** `MonadFrame.frame`
  runs a computation as one call. `Func.runOps` runs each callee in a
  frame, and `Func.run` runs the function it starts with in one. The frame
  is the monad's: the interpreter says only where a call starts and returns.
- **A monad without memory has frames that change nothing.** In the set
  monad and the tree of choices a frame is the computation itself, so M0's
  runs, `fir-ref` and their proofs are unchanged.
- **The state layer adds memory.** `StateT (Memories Mem unit) m` keeps
  `m`'s choice and UB, gives the memory effect, and makes a frame enter a
  call, run, then free the frame's allocations. A stuck path keeps the
  memories it reached; a UB path shows none. Monad morphisms lift through
  the layer.
- **Runs with memory start empty and show what they return.** Until
  observations at the end of a run are designed (#233), an observer of a
  run with memory sees its returned values only.

## Alternatives

- **Thread memory through the interpreter, as fuel is.** Every op's
  semantics would take and give memories, so every dialect and every proof
  about op semantics would change, for ops that never touch memory.
- **Free a call's stack allocations by marking each memory's allocation
  count at the call.** The interpreter would need to enumerate memory
  names, which may be infinite, such as `ptr<N>`'s.

## Consequences

- A dialect whose ops touch no memory runs in the layer by lifting its
  rules, and its runs with memory are its runs (`Func.memRuns_eq`).
- Ops that touch memory state their semantics in a monad with
  `MonadMemory`; progress, fuel monotonicity and refinement for them are
  proved over the layer, and `fir-ref` walks the layer over the tree of
  choices (#231).
