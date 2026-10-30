# `fir-ref` runs the interpreter in a tree of choices, which a monad morphism maps to the spec's set monad

Status: accepted

## Context

ADR-2026-10-29-2017 gives the interpreter a choice effect and `fir-ref` two
modes, exhaustive and scripted, and asks Lean to prove that exhaustive mode
within its budget returns exactly the run's set of outcomes, and scripted
mode a member of it. [#14](https://github.com/pmatos/funk/issues/14) states
both against one fuel budget `n`: `(run n).outcomes`.

Facts:

- The spec's meaning of a run is the interpreter, `Func.run`, in the set
  monad `SetM`, where a computation is a predicate on the ways it may end
  (`lean/Fir/Execution/Behaviour.lean`). A program cannot list a
  predicate's members.
- The interpreter is written once, against an abstract monad, and the core
  dialect's rules once, for any monad with the effects they need
  (`Core.Op.denote?`, ADR-2026-10-30-1855).
- `fir-ref run` of #10 ran the interpreter in `Except`, a monad with one
  path and no choice effect.
- An op without rules has no outcome in `SetM`, and `fir-ref` reports it
  as an error (ADR-2026-10-30-1855).

## Decision

- **A tree of choices.** `ChoiceTree ε α`
  (`lean/Fir/Execution/ChoiceTree.lean`) is a monad whose computations are
  trees: a leaf ends a path with a result, with UB, or with no outcome for
  a reason `ε`; a node `choose w k` has a subtree `k b` for each `w` bits
  `b`. `choose` and `ub` are its effects. `fir-ref` runs the core
  dialect's rules in `ChoiceTree Core.Op`, where an op without rules ends
  its path with no outcome and names itself.
- **Its meaning is the set monad's.** `ChoiceTree.toSet` maps a tree to
  the set of the ways its paths end; a path with no outcome adds nothing.
  It is a monad morphism, `ChoiceTree.toSetMorphism`, and keeps `choose` and
  `ub`.
- **The interpreter cannot tell monads apart.** `Func.run_map`
  (`lean/Fir/Execution/Morphism.lean`) proves that a monad morphism that
  maps each op's semantics in one monad to its semantics in another maps a
  function's run in the first to its run in the second.
  `Core.mapsDenote` proves that the core rules in the tree map to the core
  rules in `SetM`.
- **Two walks, proved once.** `ChoiceTree.explore` visits every path
  within a budget on the bits chosen on one path, and `ChoiceTree.script`
  follows the path that a choice sequence names
  (`lean/Fir/Execution/Modes.lean`). `explore_toSet` and `script_toSet`
  prove them sound for any tree; `Func.explore_outcomes` and
  `Func.script_outcomes` lift both to a run of the interpreter, at the fuel
  budget it runs with, for any dialect; `Core.exhaustive_outcomes` and
  `Core.scripted_outcomes` state them for the core dialect. `fir-ref`
  calls `Core.exhaustive` and `Core.scripted`, the functions these
  theorems are about. The proofs rest on `propext` and `Quot.sound`.

## Alternatives

- **A list monad that carries every path.** It enumerates, but scripted
  mode would need a second monad that reads choices, and a second proof.
  One tree gives both walks from one run.
- **Define the semantics through the tree.** It would change what the
  spec's `DialectDenote CoreDialect SetM` and its obligations mean; the
  spec is the contract.
- **Prove each mode by induction over the interpreter.** One proof per
  mode, redone whenever the interpreter changes. The morphism proof
  depends only on the monad operations the interpreter uses.

## Consequences

- An op family adds its rule to `Core.Op.denote?` or `Core.Op.exit?`, and
  `Core.mapsDenote` covers it, usually by `rfl`.
- A new effect, such as #20's call effect, needs its node in the tree, its
  image in the set monad, and its case in the morphism's proofs.
- A change to the interpreter that uses a monad operation other than
  `pure`, `bind`, `ExceptT.lift` and `liftExcept` extends
  `Func.runOps_map`'s proof.
- A node holds a function of the bits, so exhaustive mode runs the rest of
  the function once for each value it tries.
