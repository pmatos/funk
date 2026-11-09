# The core dialect's behaviour is the set instance, and a dialect that needs probabilities supplies its own behaviour model at a named seam

Status: accepted

## Context

G0 (ADR-2026-10-29-2016) names quantum and photonic processors as targets
and says no decision may close that door. S4 (ADR-2026-10-29-2008) defines
correctness as refinement over observations that each dialect supplies.

Effects and observations already come from the dialect. Behaviour and
refinement do not. A run's meaning is a set of outcomes (`SetM`, `Behaviour`
in [`Behaviour.lean`](../../lean/Fir/Execution/Behaviour.lean)), and
refinement compares those sets (`Behaviour.IsRefinedBy`,
`FuncRuns.IsRefinedBy` in
[`Refinement.lean`](../../lean/Fir/Execution/Refinement.lean)).

Sets are right for nondeterminism such as `freeze`. They are wrong for
probabilistic hardware. There, a correct target must keep the distribution
of outcomes, and not only stay inside the set of possible ones.

Many theorems of `lean/Fir` are stated over `SetM`, and M1 adds memory on
top of them. The human ruled on
[#166](https://github.com/pmatos/funk/issues/166) on 2026-11-09: name the
seam now, and generalize later.

## Decision

- **The set instance.** The core dialect's behaviour is a set of outcomes.
  Its refinement is set refinement: each outcome of the target is allowed by
  some outcome of the source (`Behaviour.IsRefinedBy`). No Lean definition
  changes. The theorems about behaviour and refinement in `lean/Fir` are
  about this instance.
- **The seam.** It has two parts, both already in the spec:
  - The interpreter is generic over its monad. `Func.run` takes any monad
    `m` with `DialectDenote d m`
    ([`Interpreter.lean`](../../lean/Fir/Execution/Interpreter.lean)).
  - The tree of choices maps to a meaning by a monad morphism
    (`ChoiceTree.toSetMorphism` in
    [`ChoiceTree.lean`](../../lean/Fir/Execution/ChoiceTree.lean)).
    `Func.run_map` carries any such morphism to the interpreter's run
    ([`Morphism.lean`](../../lean/Fir/Execution/Morphism.lean)).
- **A behaviour model.** A dialect that needs probabilistic behaviour
  supplies its own model. A model is an interpretation of the tree, or of
  the tree extended with the dialect's own effect, as a `MonadMorphism`,
  together with a refinement order on that model.
- **What a model's order must reduce to.** On the outcomes that a model gives
  with non-zero weight, its order must imply set refinement. So results
  proved for the set instance stay valid as statements about which outcomes
  are possible. They say nothing about how likely an outcome is.
- **The generalization waits.** A behaviour-model class with `SetM` as one
  instance is deferred until a real probabilistic dialect gives a second
  instance to design against.
- **The seam is tested.** The section on behaviour models in
  [`lean/FirTest/G0.lean`](../../lean/FirTest/G0.lean) maps a toy tree of
  weighted choices, `WeightedTree`, to a finite distribution, `Dist`,
  through a `MonadMorphism`. `weightedRun` applies `Func.run_map` to it
  for an arbitrary dialect. `mass_toDist` and `weights_nonneg` show that the
  result is a distribution. `support_toDist` shows that each result with
  non-zero weight is an outcome of the tree with its weights forgotten, read
  in the set instance.

## Alternatives

- **A behaviour monad that the dialect set supplies now, with its own
  refinement order, and `SetM` as M0's instance.** It would restate the
  generic results before any second instance exists to check the design. The
  ruling on #166 defers it.

## Consequences

- Memory ([#206](https://github.com/pmatos/funk/issues/206)) builds on the
  current definitions.
- The first probabilistic dialect does the generalization, and pays for
  restating whichever generic results it needs at the new generality.
- Passing set refinement does not show that a target keeps a distribution. A
  target can have the same possible outcomes with different weights. The
  dialect's own order has to catch that.
- A path of weight zero is an outcome of the set instance but not of the
  distribution, so the set of a tree can be larger than the support of its
  distribution.
- The toy has no refinement order. A real order comes with a real dialect.
- If the interpreter stops being generic over its monad, or `Func.run_map`
  changes shape, `G0.lean` stops building.
