# Memory is a state layer over the way of computing, and every function runs in a frame

Status: accepted
Tier: direction; area: semantics

## Decision

- **The memories of a run are one state:** one memory of the model for each
  memory name, with its unit width, and a stack of frames, each listing the
  stack allocations its call made.
- **Memory is an effect.** A class on the monad, `MonadMemory`, gives
  allocating, freeing, loading and storing on a named memory, and a faulting
  access is UB. A dialect whose ops touch memory states their semantics in a
  monad with that class, as it states choice and UB (ADR-2026-10-29-2030).
- **Every function runs in a frame.** The interpreter says only where a call
  starts and returns, through the frame effect `MonadFrame`, and imports
  nothing of the memory model (G0, ADR-2026-10-29-2016).
- **A monad without memory is unchanged.** In the set monad and the tree of
  choices a frame is the computation itself, so M0's runs, `fir-ref` and their
  proofs stay as they are.
- **The state layer adds memory.** `StateT` over the memories keeps the inner
  monad's choice and UB, gives the memory effect, and makes a frame enter a
  call, run it, then free the frame's stack allocations.

[semantics-m1-design.md](../decisions/semantics-m1-design.md) says how the
spec builds it, and semantics.md what holds today.

## Why

Memory had to become part of a run without a second interpreter, and the
interpreter had to free a call's stack allocations (ADR-2026-11-09-1548)
without knowing what memory is. A layer leaves every op that touches no memory,
and every proof about it, as it was.

## Rejected alternatives

- **Thread memory through the interpreter, as fuel is.** Every op's semantics
  would take and give memories, so every dialect and every proof about op
  semantics would change, for ops that never touch memory.
- **Free a call's stack allocations by marking each memory's allocation count
  at the call.** The interpreter would need to enumerate memory names, which
  may be infinite, such as those of `ptr<N>`.
