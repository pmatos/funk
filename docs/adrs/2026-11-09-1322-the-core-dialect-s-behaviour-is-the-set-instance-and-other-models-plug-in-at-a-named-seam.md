# The core dialect's behaviour is the set instance, and a dialect that needs probabilities supplies its own behaviour model at a named seam

Status: accepted
Tier: direction; area: semantics

## Decision

- **The set instance.** The core dialect's behaviour is a set of outcomes.
  Its refinement is set refinement: each outcome of the target is allowed by
  some outcome of the source (`Behaviour.IsRefinedBy`). The theorems about
  behaviour and refinement in `lean/Fir` are about this instance.
- **The seam.** The interpreter is generic over its monad (`Func.run` takes
  any monad with `DialectDenote d m`), and the tree of choices maps to a
  meaning by a monad morphism, which `Func.run_map` carries to the run.
- **A behaviour model.** A dialect that needs probabilistic behaviour
  supplies its own model: an interpretation of the tree, or of the tree
  extended with its own effect, as a `MonadMorphism`, with a refinement
  order on that model. On the outcomes it gives with non-zero weight, the
  order must imply set refinement, so results proved for the set instance
  stay valid as statements about which outcomes are possible.
- **The generalization waits.** A behaviour-model class with `SetM` as one
  instance waits for a real probabilistic dialect, which restates the generic
  results it needs.
- **The seam is tested.** `lean/FirTest/G0.lean` maps a toy tree of weighted
  choices to a finite distribution through `Func.run_map`, so it stops
  building if the seam changes shape.

The human ruled this on 2026-11-09 (#166): name the seam now, and generalize
later. [semantics-refinement.md](../decisions/semantics-refinement.md#behaviour-models)
states what holds.

## Why

G0 (ADR-2026-10-29-2016) names quantum and photonic processors as targets,
and S4 (ADR-2026-10-29-2008) makes correctness refinement over observations
each dialect supplies. Sets are right for nondeterminism such as `freeze`,
and wrong for probabilistic hardware, where a correct target must keep the
distribution of outcomes. Passing set refinement does not show that, so the
dialect's own order has to.

## Rejected alternatives

- **A behaviour monad that the dialect set supplies now, with its own
  refinement order and `SetM` as M0's instance.** It would restate the
  generic results before any second instance exists to check the design.
