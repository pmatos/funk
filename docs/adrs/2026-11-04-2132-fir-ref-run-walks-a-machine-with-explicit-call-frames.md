# `fir-ref run` walks a machine with explicit call frames in place of the spec's modes

Status: accepted; refined by ADR-2026-11-05-0442
Tier: implementation; area: fir-ref

## Context

`fir-ref run` reports a run through one of the spec's three modes,
`Core.scripted`, `Core.exhaustive` and `Core.sampled`
([`lean/Fir/Core/Modes.lean`](../../lean/Fir/Core/Modes.lean),
ADR-2026-10-30-2218, ADR-2026-10-31-0002). Each builds the run's tree of
choices with `Func.run` and walks it.

The spec's interpreter, `Func.runOps`, is written once for any monad. In
the tree of choices each step is a bind whose continuation runs the next
step, and a call runs its callee inside its caller's bind. Compiled, it
takes stack for every step and for every level of calls, and
`ChoiceTree.sample` and `ChoiceTree.explore` take stack for every choice on
a path. So a loop or a recursion that never ends aborted `fir-ref run` with
"Stack overflow detected" above about 1.5 to 3 million steps on the default
stack, and far sooner with `LEAN_STACK_SIZE_KB=256`, instead of reporting
fuel exhaustion ([#47](https://github.com/pmatos/funk/issues/47)).

ADR-2026-10-30-1450 gives the way out: `fir-ref` runs an implementation
proved equal to the spec's function and registered with `@[csimp]`, and
the spec keeps its definitions. Two facts choose where:

- The spec compiles the three modes before any theorem of `FirRef`, so a
  `@[csimp]` theorem on `Func.runOps` or `Func.run` would not change what
  they call, as for `Fir.parse` (ADR-2026-10-30-1450).
- `Func.runOps` is generic in the monad; a loop can stand for it only in
  the tree of choices.

## Decision

- **A machine runs the steps.** `FirRef.Machine.advance`
  ([`lean/FirRef/Machine.lean`](../../lean/FirRef/Machine.lean)) takes the
  steps of a run in a loop whose recursive calls are tail calls. Its state
  is what the function that runs has left to do (`Cur`) and a list of
  frames, one for each caller that waits for its callee. Each step is one
  case of `Func.runOps`'s definition and calls the same functions: the
  dialect's rules, `Env.operands`, `Env.bind`, `Func.jump` and
  `Func.enter`. It stops at the end of a path or at a choice, and then
  gives the state that the run goes on from for each value of the choice.
- **A state stands for the spec's computation.** `Cur.denote` is the spec's
  computation of what the function that runs has left, and `kont` adds the
  waiting callers' continuations. `Machine.advance_tree` proves, by
  functional induction on `advance` and one equation of `Func.runOps` per
  case, that where the machine stops stands for the spec's tree of the
  state.
- **The modes walk the machine.** `Machine.scripted`, `Machine.exhaustive`
  and `Machine.sampled`
  ([`lean/FirRef/RunModes.lean`](../../lean/FirRef/RunModes.lean)) walk
  its states in loops of tail calls: scripted and sampled modes with an
  accumulator, exhaustive mode with a work list of states and of each
  choice's values still to visit, in the order that the spec visits the
  paths. Like the spec, it goes on from a value only when it gets to it,
  and stops at the first path over its budget. For every dialect, each is
  proved to give what the spec's `ChoiceTree.script`, `explore` or
  `sample` gives on the tree of the run.
- **`FirRef.Run` registers them for the core dialect.** It defines
  `FirRef.runScripted`, `FirRef.runExhaustive` and `FirRef.runSampled`
  with the types of the spec's modes and registers
  `@[csimp] scripted_eq_runScripted : @Core.scripted = @runScripted`,
  `exhaustive_eq_runExhaustive` and `sampled_eq_runSampled`, before
  `runBytes`, which calls the modes. These theorems name the core dialect,
  and in `lean/FirRef/` only `fir-ref`'s command line may (G0,
  ADR-2026-11-03-0600), so they are not in a module that `FirRef.Fast`
  imports, as ADR-2026-10-30-1450 places the others.

## Alternatives

- **A `@[csimp]` theorem on `Func.runOps` or `Func.run`.** The modes,
  compiled in the spec, would still call the spec's interpreter.
- **A machine that builds the spec's tree lazily, walked by the spec's
  `ChoiceTree.script`, `explore` and `sample`.** Sampled and exhaustive
  modes would still take stack for every choice.
- **Write `Func.runOps` as a machine in the spec.** The spec would lose its
  readable interpreter, which its theorems on runs, progress and
  refinement are about. ADR-2026-11-02-0836 rejected a machine with a
  stack of frames for the spec on the same ground; here the machine is
  only what `fir-ref` runs, proved equal to the spec's interpreter.
- **A larger stack.** It moves the limit instead of removing it
  (ADR-2026-10-30-1450).

## Consequences

- `fir-ref run` reports fuel exhaustion at any budget. Its frames and
  environments are on the heap, so a deep recursion costs memory, not
  stack.
- A change to `Func.runOps`, `Func.run`, `ChoiceTree.script`, `explore` or
  `sample`, or to the three modes breaks these proofs, and so the build,
  until the machine follows. A new mode of `fir-ref run` needs its own walk
  of the machine and its own `@[csimp]` theorem.
- `Machine.c` also compiles the functions that the proofs use
  (`Cur.denote`, `kont`), which call `Func.runOps`; `fir-ref` never calls
  them. So the evidence that `fir-ref` runs the machine is in what its
  `main` reaches: `lean/.lake/build/ir/FirRef/Run.c` calls the three
  walkers, and no copy of `Func.runOps`, `Func.run` or the spec's modes is
  reached.
- Code that calls the spec's modes and is compiled before `FirRef.Run`,
  or in a module that does not import it, still runs the spec's code.
- `lean/FirTest/RunSteps.lean` runs each mode for 1,000,000 steps on a loop
  and on a recursion that never end, in Lean's interpreter during the
  build.
