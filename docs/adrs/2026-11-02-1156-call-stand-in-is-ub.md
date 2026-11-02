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
hold for it. This extends ADR-2026-11-02-0836, which left the stand-in
open.

Facts that constrain the stand-in:

- `Op.denote?` is written once for any monad with the choice and UB
  effects, so the set monad's instance and the tree of choices that
  `fir-ref` runs agree on it (`Core.mapsDenote`).
- `OpTotal` asks an outcome on every operand vector of every op instance,
  `call @g` at `ptr` types included, and `ptr` has no values in M0. So no
  rule that only returns values is total.
- The set monad has no module, so no rule there can run the callee.

ADR-2026-10-30-1855 rejects always-UB, and may-do-anything, for an op
without rules: it gives the op a meaning that it does not have, it lets an
exception pass for lawful, since totality and monotonicity are all of an
exception's obligations, and `fir-ref` would report it. With this
stand-in, `call` does pass `OpTotal` and `OpMonotone`, vacuously. That is
acceptable here only because `call`'s meaning is not missing:
`DialectCall CoreDialect` gives it its callee's run, `fir-ref` never
reaches the stand-in, and the facts about calls are proved over the runs
of functions (`Core.progress`, `Core.neverStuck`, and #20's refinement
theorems).

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
- **Every defined result.** It is not total at a `ptr` result, and as a
  source it is refined by `const 0`, so it shares UB's hazard below.
- **No op-level obligation for an op with a callee.** `total` and
  `monotone` would range over ops whose `callee?` is `none`, and `call`
  would keep no `denote` entry. It is the only choice under which no
  op-level statement can read a meaning into `call`. #20 asks that both
  obligations hold for `call`'s stand-in, so changing this is a direction
  call for the human.

## Consequences

- The stand-in is the top of the refinement order: every computation
  refines it (`Core.call_isRefinedBy`). Its two obligations hold
  trivially and carry no information about calls.
- Any statement that reads `call`'s `denote` as a source, such as a
  rewrite rule proved op by op, holds for every target and says nothing
  about a real call: it would prove the rewrite of `call @g` to `const 0`.
  Such statements must exclude ops whose `callee?` is `some`. Facts about
  calls are proved over the runs of functions: `Core.progress` and
  `Core.neverStuck`, and #20's refinement theorems for refined arguments
  and for a refined callee.
- A reader of `Op.denote?` sees `call` as UB there. The prose beside it, in
  the spec's section on calls, says that the interpreter never runs it.
- `fir-ref`'s results do not depend on the stand-in.
