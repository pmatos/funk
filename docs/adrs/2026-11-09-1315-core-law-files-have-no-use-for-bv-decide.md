# The core law files have no use for `bv_decide` today

Status: accepted
Tier: implementation; area: semantics

## Context

Issue [#175](https://github.com/pmatos/funk/issues/175) asked for the
bitvector lemmas of the core dialect's law files to be proved by
`bv_decide` wherever that shortens them. ADR-2026-10-30-1838 allows the
native axioms that this adds.

A survey of `lean/Fir/Core/` found very few such lemmas. The `*Laws.lean`
files prove facts about poison, refinement and the set monad, by case
analysis on `PoisonOr` and `Ev`.

Only three proofs in the core dialect reason about bits:

| Lemma | Width | `bv_decide` |
| --- | --- | --- |
| `bitVec_one_cases` in `TextLaws.lean` | 1 | proves it |
| The side goals of `divEv_zero_one` in `DivLaws.lean` | any `w` | fails |
| `shiftValues_msb` in `Bitwise.lean` | any `w` | fails |

`bv_decide` needs a width that is a literal. At a symbolic width it treats
the terms that depend on the width as opaque variables and reports a
spurious counterexample.

`Op.decode_encode` uses `bitVec_one_cases`, so the round trip for the core
dialect rests on that lemma.

## Decision

- `bitVec_one_cases` is proved by `revert v; decide`, not by `bv_decide`.
- The two symbolic-width proofs stay as they are.
- No other proof in the core law files changes.

## Alternatives

- `bv_decide` on `bitVec_one_cases`. It is one line too, but it adds a native
  axiom under the core round trip and trusts the compiler for a fact with
  two cases. `decide` needs only `propext` and `Quot.sound`.

## Consequences

- The lemma's proof goes from five lines to one, and no axiom pin changes.
- `bv_decide` is still unused in `lean/Fir`. It remains the tool that the
  roadmap names as the bar for admitting rewrite rules.
