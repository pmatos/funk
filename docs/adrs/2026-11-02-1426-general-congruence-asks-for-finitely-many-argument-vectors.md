# The general congruence theorem asks for finitely many argument vectors

Status: accepted
Tier: implementation; area: semantics

## Context

Congruence in the callee (ADR-2026-11-02-1350) is proved once for every
dialect, by `Func.runs_replaceBody_isRefinedBy`, then for the core
dialect. The proof treats every call of the replaced callee `@g` as a
black box, and a black box needs a `bound`: on each argument vector, the
new `@g` diverges, or none of its runs with `bound` steps or more runs
out of fuel.

Facts that constrain it:

- A behaviour says nothing of steps, while a caller goes on with the
  steps that its callee leaves (ADR-2026-11-02-0836).
- Divergence is running out of fuel at every budget, which assumes
  finitely many ways to go at each step
  ([`lean/Fir/Execution/Behaviour.lean`](../../lean/Fir/Execution/Behaviour.lean)).
- Each argument vector has its own budget, since a run that runs out of
  fuel with more steps runs out with fewer (`Func.runs_exhausted_down`).
  Without a bound on how many there are, one budget may not serve them
  all: a caller whose arguments to `@g` grow without limit can make the
  new `@g` run longer and longer before it returns.

## Decision

`Func.runs_replaceBody_isRefinedBy` asks that `@g`'s parameter types have
finitely many argument vectors:
`∃ L : List (HVector toType (g.params.map (·.2))), ∀ a, a ∈ L`. Then one
budget bounds every run of the new `@g` that does not diverge
(`exists_common_bound`).

Every core type has finitely many values: poison and the `2 ^ N` bit
vectors of `iN`, and none of `ptr`. `Core.argVectors` lists them, and
`Core.mem_argVectors` meets the hypothesis.

## Alternatives

- **König's lemma over the tree of choices.** It could cover every
  dialect whose choices each have finitely many options, but it needs an
  infinite path through `ChoiceTree` runs at every budget, which the spec
  does not have. M0's types do not need it.

## Consequences

- A dialect with a type of infinitely many values, such as memory (S3),
  cannot use the general theorem as it is. It needs König's lemma or an
  argument of its own.
- Refined arguments, #20's other theorem, need no finiteness: they
  replace no callee.
