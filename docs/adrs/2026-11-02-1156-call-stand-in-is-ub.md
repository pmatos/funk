# The stand-in for `call` in the set monad is immediate UB

Status: accepted

## Context

ADR-2026-11-02-0836 gives `call` its meaning through the call effect: the
interpreter runs the callee that `DialectCall CoreDialect` names, and never
runs `call`'s `denote`. But the op-level obligations `OpTotal` and
`OpMonotone` look at `denote` in the set monad, and
`LawfulDialectPoison CoreDialect` asks them of every op. So `call` needs an
entry in `Core.Op.denote?`: a stand-in that the interpreter never runs.
[#20](https://github.com/pmatos/funk/issues/20) asks that both obligations
hold for it.

Facts that constrain the stand-in:

- `Op.denote?` is written once for any monad with the choice and UB
  effects, so the set monad's instance and the tree of choices that
  `fir-ref` runs agree on it (`Core.mapsDenote`).
- `OpTotal` asks an outcome on every operand vector of every op instance,
  `call @g` at `ptr` types included, and `ptr` has no values in M0. So no
  rule that only returns values is total.
- The set monad has no module, so no rule there can run the callee.

ADR-2026-10-30-1855 rejects "always UB" for an op _without_ rules, because
`fir-ref` would report that UB as the op's meaning. `call` has rules, its
callee's, and `fir-ref` never reaches its `denote`.

## Decision

`call`'s entry in `Core.Op.denote?` is `Core.callStandIn`: immediate UB on
every operand vector, with the reason
`call's stand-in, which the interpreter never runs`
([`lean/Fir/Core/Call.lean`](../../lean/Fir/Core/Call.lean)). It is total
and monotone (`Core.call_total`, `Core.call_monotone`), and every core op
is total (`Core.Op.total_all`).

## Alternatives

- **No entry (`none`).** `call` would have no outcome in the set monad,
  `OpTotal` would fail, and `Op.hasRules` would call it an op without
  rules.
- **Poison results.** Not total: a `call` with a `ptr` result has no
  poison to return. It would also read as a propagating rule, which
  `call`, an exception, does not have.
- **Any result or UB, built from choices.** Total and monotone, but UB
  already allows every result, so it says no more than UB, and it adds
  choice nodes and a `Core.mapsDenote` case for a rule that never runs.

## Consequences

- Every behaviour of a call refines the stand-in, so its two obligations
  claim nothing about calls. The facts about calls are stated about the
  runs of functions: `Core.progress` and `Core.neverStuck`, and #20's
  refinement theorems for refined arguments and for a refined callee.
- A reader of `Op.denote?` sees `call` as UB there. The prose beside it, in
  the spec's section on calls, says that the interpreter never runs it.
- `fir-ref`'s results do not depend on the stand-in.
