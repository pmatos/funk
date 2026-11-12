# A call has no op-level rule: its meaning is its callee's run

Status: accepted
Tier: direction; area: semantics

## Context

ADR-2026-11-02-0836 gives a call its meaning through the call effect: the
interpreter runs the callee that `DialectCall` names, and never runs the
op's `denote`. An earlier ADR then gave `call` a stand-in `denote` in
the set monad, immediate UB, so that the op-level obligations `OpTotal`
and `OpMonotone`, which `LawfulDialectPoison` asked of every op, would
hold for it.

The stand-in claimed a meaning that a call does not have: a call is not
immediate UB. The two obligations it met said nothing about calls. As a
source it was refined by every computation (`Core.call_isRefinedBy`), so
a statement proved op by op, such as a rewrite rule, would hold for every
rewrite of a call. What a call does is covered at function level:
`Core.progress`, `Core.neverStuck`, `Core.fuelMonotone`,
`Core.args_isRefinedBy` and `Core.replaceBody_isRefinedBy`.

The human ruled on 2026-11-02, on
[#20](https://github.com/pmatos/funk/issues/20), for the alternative that
the earlier ADR listed last: no op-level obligation for an op with a
callee.

## Decision

- `call` has no entry in `Core.Op.denote?`: it gives `none`, as for an op
  without rules. In the set monad, `call`'s `denote` has no outcome. The
  interpreter never reaches it: it runs the callee of every op that has
  one before it looks at `denote`
  ([`lean/Fir/Execution/Interpreter.lean`](../../lean/Fir/Execution/Interpreter.lean)).
- The fields `total` and `monotone` of `LawfulDialectPoison` cover only
  the ops that the interpreter runs by their own rule: terminators, and
  ops with no callee (`isTerminator op = true ∨ callee? op = none`).
- So do the hypotheses that ask every op to be total or monotone: those
  of the progress proof with calls (`Module.calls_hasPath`,
  `Func.progress_of_inModule`) and those of the refinement engine
  (`Func.runOps_allowed`, `Func.runOps_allowedBelow`,
  `Func.runs_isRefinedBy_of_calls`, `Func.runs_args_isRefinedBy`,
  `Func.runs_replaceBody_isRefinedBy`). Their proofs used the obligations
  only for such ops.
- `Core.callStandIn`, its reason `Core.callStandInReason`,
  `Core.call_denote`, which stated it, `Core.call_total`,
  `Core.call_monotone` and `Core.call_isRefinedBy` are removed, with
  `lean/Fir/Core/CallLaws.lean`, which held them. `Core.Op.total_all`
  and `Core.Op.monotone_all` hold for every core op that meets the guard:
  every core op but `call`.
- Where the spec counts which ops have rules (`Core.Op.hasRules`), an op
  with a callee has them: its meaning is its callee's run.

It replaces that earlier ADR, now deleted (`INDEX.md`, Removed). It
refines ADR-2026-10-30-0818,
which asked every op to be total and monotone; ADR-2026-11-02-0836, whose
consequences describe the stand-in; and the rule for ops without rules
([fir-ref.md](../decisions/fir-ref.md#an-op-without-rules)), since a
`call` with `none` in `Op.denote?` is not an op without rules.

## Consequences

- No op-level statement reads a meaning into a call. A statement proved
  op by op must leave out the ops with a callee, as the class does. M1's
  rewrite rules need the same exclusion, which
  [#96](https://github.com/pmatos/funk/issues/96) tracks.
- Progress through a call rests on the induction over its callee's run
  (`Module.calls_hasPath`), and refinement on the engine's induction over
  the callee, or on a black box. Neither needs an op-level fact about
  `call`.
- `fir-ref`'s results do not change: no run reaches `call`'s `denote`.
