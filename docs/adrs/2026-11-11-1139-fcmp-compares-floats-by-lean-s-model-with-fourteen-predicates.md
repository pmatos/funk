# fcmp compares floats by Lean's model, with fourteen predicates

Status: accepted
Tier: direction; area: semantics

## Context

#229 adds the ordered and unordered float comparisons. IEEE 754 §5.11
compares the numbers that two floats encode: `-0` equals `+0`, and a NaN
is unordered with everything, itself included. LLVM's `fcmp` has sixteen
predicates: seven ordered, seven unordered, and the constants `false` and
`true`. ADR-2026-11-09-1549 defines fir's float ops on Lean's float
model, whose `UnpackedFloat.compare` gives `none` for an unordered pair.
#229's first stage checked that `compare` gives the IEEE 754 order at
every format it tried.

## Decision

- `%r: i1 = fcmp P %a, %b` takes two values of one float type and gives
  an `i1`. `P` is one of fourteen predicates, LLVM's names: `oeq`, `one`,
  `olt`, `ole`, `ogt`, `oge`, `ord`, `ueq`, `une`, `ult`, `ule`, `ugt`,
  `uge` and `uno`.
- The spec unpacks both operands with Lean's model and compares them with
  `UnpackedFloat.compare`. An `o` predicate is false on an unordered pair
  and a `u` predicate true. Otherwise `eq`, `ne`, `lt`, `le`, `gt` and
  `ge` say how the two numbers compare. `ord` holds when the pair is
  ordered, and `uno` when it is not.
- A format that the model does not accept, which validation rejects
  (ADR-2026-11-11-0950), has every pair unordered, so that the rule is
  total.
- `fcmp` never gives a NaN and is never UB. A poison operand gives a
  poison result. It is pure (ADR-2026-11-09-1541).
- LLVM's `false` and `true` predicates are not predicates of `fcmp`: they
  do not look at their operands, and `const false` and `const true` write
  them.

## Alternatives

- **Compare the bits directly.** Simple, but a second definition of the
  order, beside the model that ADR-2026-11-09-1549 builds on.
- **All sixteen of LLVM's predicates.** Two of them compare nothing, and
  each would be one more case in every layer.

## Consequences

- The comparisons rest on the model, as the arithmetic of #229 will.
- `fcmp`'s result is never a NaN, so `funk` and `fir-ref` compare it
  differentially before #219 decides how a NaN result is judged.
