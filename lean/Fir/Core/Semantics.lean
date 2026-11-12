import Fir.Core.Arith
import Fir.Core.Wrap
import Fir.Core.Freeze
import Fir.Core.Bitwise
import Fir.Core.Width
import Fir.Core.Div
import Fir.Core.Compare
import Fir.Core.FloatCompare
import Fir.Core.FloatArith
import Fir.Core.FloatBitcast
import Fir.Core.FloatOfInt
import Fir.Core.Control
import Fir.Core.Branch
import Fir.Core.Call
import Fir.Core.Text

/-!
# The core dialect's semantics

This section gives every core op its meaning in the set of the ways a run
may end, by sending each op to the rule of its family. The rules are
written once, for every way of computing that has the effects they ask
for: one table for the ops that are not terminators, and one for the
terminators. `freeze`, the float arithmetic, whose NaN results are
chosen, and the conversions from integers, which choose a NaN only at a
format that validation rejects, ask for the choice effect, and the divisions,
`cond_br` and `unreachable` for the UB effect, so the spec and the tree of choices that
`fir-ref run` computes in share them.

* Each op that is not a terminator has the rule of its family, from the
  arithmetic rules to the width change rules. `call` has none: its meaning
  is its callee's run.
* Each terminator has the rule of the control-flow rules or the branch
  rules.
* An op has rules when one of the two tables gives it one, or when it
  calls a function. Every core op has rules: each family gave its ops
  theirs, and the call rules name the callee of `call`.

An op has no rules when its dialect's semantics gives it none. The rule for
such an op, first written while its family had not landed, is the one the spec
keeps for every dialect (`docs/decisions/fir-ref.md#an-op-without-rules`):

* In the spec, it has no outcome: on every operand vector, its meaning is
  the empty set. That is not a stand-in semantics. The totality obligation
  rejects it, as it rejects the semantics with no outcome in the section
  on semantics the obligations reject. So a dialect's poison obligations
  cannot be proved while one of its valid op instances that runs by its
  own rule (a terminator, or an op that calls no function) lacks its
  rules, unless one of its operand types has no value. No core op lacks
  them, and the core dialect's poison obligations are proved.
* Only totality, a result on defined operands, progress and the poison
  obligations as a whole, which include totality, reject such an op. The
  other properties hold of it trivially, because a computation with no
  outcome meets every bound on what may happen: poison propagation and
  monotonicity on their own hold of the op, no stuck path and fuel
  monotonicity hold of any function that reaches it, and such a function
  refines every source. So none of these statements
  is claimed of an op without rules, or of a function that reaches one.
  The general theorems of fuel monotonicity and no stuck path cover such a
  function too, but only vacuously on the paths that reach the op: they
  say nothing of how it behaves.
* A run that reaches such an op has no way to end on that path; when every
  path does, progress fails. So progress and no stuck path were proved
  first for every valid core function without a `call` op, while `call`
  had no rules, and are proved now for every function of every valid core
  module, calls and recursion included.
* `fir-ref run` prints no outcome for a run that reaches such an op. It says
  that the op has no execution rules, as an error
  (`docs/decisions/fir-ref-command-line.md#fir-ref-run`).

`call` takes its meaning from the call effect, which the interpreter runs
(ADR-2026-10-29-2009). The interpreter runs the callee of every op that
has one before it looks at the op's own meaning, so `call` has no rule
here, and its meaning in the set of the ways a run may end has no
outcome, which no run reaches. It has no op-level obligation either: the
poison obligations ask totality and monotonicity only of terminators and
of ops that call no function (ADR-2026-10-29-2006). The obligations of
each family are proved in sections of their own after this one, from the
constant obligations to the branch obligations.
-/

namespace Fir.Core

variable {m : Type → Type} [Monad m]

/-- The rule of each core op that is not a terminator, in any monad with
the choice and UB effects; `none` for `call`, whose meaning is its
callee's run, and for the terminators. -/
def Op.denote? [MonadChoice m] [MonadUB m] : (op : Op) →
    Option (HVector toType (Fir.sig (d := CoreDialect) op) →
      m (HVector toType (Fir.returnTypes (d := CoreDialect) op)))
  | .const w v => some fun _ => pure (.cons (constValue w v) .nil)
  | .fconst e m v => some fun _ => pure (.cons (fconstValue e m v) .nil)
  | .poison w => some fun _ => pure (.cons (poisonValue w) .nil)
  | .add _ f => some fun
    | .cons a (.cons b .nil) => pure (.cons (addWith f a b) .nil)
  | .sub _ f => some fun
    | .cons a (.cons b .nil) => pure (.cons (subWith f a b) .nil)
  | .mul _ f => some fun
    | .cons a (.cons b .nil) => pure (.cons (mulWith f a b) .nil)
  | .sdiv _ x => some (ruleOfEv (sdivWith x))
  | .udiv _ x => some (ruleOfEv (udivWith x))
  | .srem _ => some (ruleOfEv sremValues)
  | .urem _ => some (ruleOfEv uremValues)
  | .freeze _ => some fun
    | .cons a .nil => do
      let v ← freezeValue a
      pure (.cons v .nil)
  | .and _ => some fun
    | .cons a (.cons b .nil) => pure (.cons (andValues a b) .nil)
  | .or _ => some fun
    | .cons a (.cons b .nil) => pure (.cons (orValues a b) .nil)
  | .xor _ => some fun
    | .cons a (.cons b .nil) => pure (.cons (xorValues a b) .nil)
  | .shl _ => some fun
    | .cons a (.cons b .nil) => pure (.cons (shlValues a b) .nil)
  | .lshr _ => some fun
    | .cons a (.cons b .nil) => pure (.cons (lshrValues a b) .nil)
  | .ashr _ => some fun
    | .cons a (.cons b .nil) => pure (.cons (ashrValues a b) .nil)
  | .icmp p _ => some fun
    | .cons a (.cons b .nil) => pure (.cons (icmpValues p a b) .nil)
  | .fcmp p _ _ => some fun
    | .cons a (.cons b .nil) => pure (.cons (fcmpValues p a b) .nil)
  | .fbin o _ _ => some fun
    | .cons a (.cons b .nil) => do
      let v ← fbinValues o a b
      pure (.cons v .nil)
  | .funary o _ _ => some fun
    | .cons a .nil => do
      let v ← funaryValue o a
      pure (.cons v .nil)
  | .fma _ _ => some fun
    | .cons a (.cons b (.cons c .nil)) => do
      let v ← fmaValues a b c
      pure (.cons v .nil)
  | .select _ => some fun
    | .cons c (.cons a (.cons b .nil)) => pure (.cons (selectValues c a b) .nil)
  | .zext _ n => some fun
    | .cons a .nil => pure (.cons (zextValue n a) .nil)
  | .sext _ n => some fun
    | .cons a .nil => pure (.cons (sextValue n a) .nil)
  | .trunc _ n => some fun
    | .cons a .nil => pure (.cons (truncValue n a) .nil)
  | .toBits _ _ => some fun
    | .cons a .nil => pure (.cons (bitcastValue a) .nil)
  | .ofBits _ _ => some fun
    | .cons a .nil => pure (.cons (bitcastValue a) .nil)
  | .sitofp _ e m => some fun
    | .cons a .nil => do
      let v ← intToFloat e m true a
      pure (.cons v .nil)
  | .uitofp _ e m => some fun
    | .cons a .nil => do
      let v ← intToFloat e m false a
      pure (.cons v .nil)
  | _ => none

/-- The rule of each core terminator, in any monad with the UB effect;
`none` for every op that is not a terminator. -/
def Op.exit? [MonadUB m] : (op : Op) →
    Option (HVector toType (Fir.sig (d := CoreDialect) op) → m Exit)
  | .br => some fun _ => pure brExit
  | .condBr => some fun
    | .cons c .nil => exitOfEv (condBrExit c)
  | .ret _ => some fun _ => pure retExit
  | .unreachable => some fun _ => exitOfEv unreachableExit
  | _ => none

/-- The op has rules: as an op that is not a terminator, as a terminator,
or as an op that calls a function, whose meaning is its callee's run. It
looks at the rules in the set monad, which has the effects of choice and
UB that the rules of `freeze`, the float arithmetic, the divisions and
`cond_br` ask for. -/
def Op.hasRules (op : Op) : Bool :=
  (op.denote? (m := SetM)).isSome || (op.exit? (m := SetM)).isSome || op.callTarget?.isSome

-- Every core op has rules: one instance of each, `add` with each of its
-- flags, and `icmp` and `fcmp` with each of their predicates among them. `call`'s are
-- its callee's run: it has no entry in `Op.denote?`.
#guard (samples.filter Op.hasRules).map Op.name == samples.map Op.name
#guard WrapFlags.all.all fun f => (Op.add 1 f).hasRules && (Op.sub 7 f).hasRules
#guard Pred.all.all fun p => (Op.icmp p 1).hasRules
#guard FPred.all.all fun p => (Op.fcmp p 8 23).hasRules && (Op.fcmp p 1 0).hasRules
#guard [FBin.fadd, .fsub, .fmul, .fdiv, .frem, .fmod].all fun o => (Op.fbin o 8 23).hasRules && (Op.fbin o 1 0).hasRules
#guard [FUnary.fneg, .fabs, .sqrt].all fun o => (Op.funary o 5 10).hasRules
#guard (Op.fma 11 52).hasRules
#guard (Op.toBits 8 23).hasRules && (Op.ofBits 11 52).hasRules && (Op.ofBits 1 0).hasRules
#guard (Op.sitofp 32 8 23).hasRules && (Op.uitofp 128 5 10).hasRules && (Op.sitofp 1 1 0).hasRules
#guard (Op.br).hasRules && (Op.condBr).hasRules && (Op.unreachable).hasRules &&
  (Op.call "f" [.int 8] [.int 8]).hasRules &&
  (Op.call "f" [] [.ptr 0]).hasRules
#guard ((Op.call "f" [.int 8] [.int 8]).denote? (m := SetM)).isNone

end Fir.Core

namespace Fir

/-- The core dialect's semantics in the set monad: each op's rule, and no
outcome where `Op.denote?` or `Op.exit?` gives none, as for `call`, whose
`denote` no run reaches. -/
instance : DialectDenote CoreDialect SetM where
  denote op args := match op.denote? (m := SetM) with
    | some rule => rule args
    | none => fun _ => False
  exit op args := match op.exit? (m := SetM) with
    | some rule => rule args
    | none => fun _ => False

/-- The core ops that call a function: `call @g` calls `@g`. -/
instance : DialectCall CoreDialect := ⟨Core.Op.callTarget?⟩

end Fir
