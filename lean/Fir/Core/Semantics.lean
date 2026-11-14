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
import Fir.Core.FloatConvert
import Fir.Core.Pointer
import Fir.Core.FloatToInt
import Fir.Core.Control
import Fir.Core.Branch
import Fir.Core.Call
import Fir.Core.TextSamples

/-!
# The core dialect's semantics

This section gives every core op its meaning in the set of the ways a run
may end, by sending each op to the rule of its family. The rules are
written once, for every way of computing that has the effects they ask
for: one table for the ops that are not terminators, and one for the
terminators. `freeze`, the float arithmetic and the conversions between
formats, whose NaN results are chosen, as is a zero's sign under `nsz`,
and the conversions from integers,
which choose a NaN only at a format that validation rejects, ask for the
choice effect, and the divisions,
`cond_br` and `unreachable` for the UB effect, so the spec and the tree of choices that
`fir-ref run` computes in share them.

* Each op that is not a terminator has the rule of its family, from the
  arithmetic rules to the width change rules. `call` has none: its meaning
  is its callee's run. `alloca` has none either: it allocates, so its rule
  needs the memory effect, and is one of the core's rules with memory.
* Each terminator has the rule of the control-flow rules or the branch
  rules.
* An op has rules when one of the two tables gives it one, when it calls
  a function, or when it touches memory. Every core op has rules: each
  family gave its ops theirs, the call rules name the callee of `call`, and
  `alloca` has its rule with memory.

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

/-- The core ops that touch memory: `alloca`, which allocates. Each has a
rule only in a monad with the memory effect (the section on the core's rules
with memory). -/
def Op.touchesMemory : Op → Bool
  | .alloca .. => true
  | _ => false

/-- The rule of each core op that is not a terminator, in any monad with
the choice and UB effects; `none` for `call`, whose meaning is its
callee's run, for `alloca`, whose rule needs memory, and for the
terminators. -/
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
  | .fcmp p fl _ _ => some fun
    | .cons a (.cons b .nil) => pure (.cons (fcmpValues p fl a b) .nil)
  | .fbin o fl _ _ => some fun
    | .cons a (.cons b .nil) => do
      let v ← fbinValues o fl a b
      pure (.cons v .nil)
  | .funary o fl _ _ => some fun
    | .cons a .nil => do
      let v ← funaryValue o fl a
      pure (.cons v .nil)
  | .fma fl _ _ => some fun
    | .cons a (.cons b (.cons c .nil)) => do
      let v ← fmaValues fl a b c
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
  | .fpext e m e' m' | .fptrunc e m e' m' => some fun
    | .cons a .nil => do
      let v ← convertFloat e m e' m' a
      pure (.cons v .nil)
  | .ptradd _ _ => some fun
    | .cons p (.cons k .nil) => pure (.cons (ptraddValue p k) .nil)
  | .fptosi e m _ => some fun
    | .cons a .nil => pure (.cons (floatToInt e m true a) .nil)
  | .fptoui e m _ => some fun
    | .cons a .nil => pure (.cons (floatToInt e m false a) .nil)
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
as an op that calls a function, whose meaning is its callee's run, or as an
op that touches memory, whose rule is its rule with memory. It looks at the
rules in the set monad, which has the effects of choice and UB that the
rules of `freeze`, the float arithmetic, the divisions and `cond_br` ask
for. -/
def Op.hasRules (op : Op) : Bool :=
  (op.denote? (m := SetM)).isSome || (op.exit? (m := SetM)).isSome || op.callTarget?.isSome ||
    op.touchesMemory

-- Every core op has rules: one instance of each, `add` with each of its
-- flags, and `icmp` and `fcmp` with each of their predicates among them. `call`'s are
-- its callee's run, and `alloca`'s is its rule with memory: neither has an
-- entry in `Op.denote?`.
#guard (samples.filter Op.hasRules).map Op.name == samples.map Op.name
#guard WrapFlags.all.all fun f => (Op.add 1 f).hasRules && (Op.sub 7 f).hasRules
#guard Pred.all.all fun p => (Op.icmp p 1).hasRules
#guard FPred.all.all fun p => (Op.fcmp p {} 8 23).hasRules && (Op.fcmp p {} 1 0).hasRules
#guard [FBin.fadd, .fsub, .fmul, .fdiv, .frem, .fmod].all fun o =>
  (Op.fbin o {} 8 23).hasRules && (Op.fbin o { nnan := true } 1 0).hasRules
#guard [FUnary.fneg, .fabs, .sqrt].all fun o => (Op.funary o { nsz := true } 5 10).hasRules
#guard (Op.fma { ninf := true } 11 52).hasRules
#guard (Op.toBits 8 23).hasRules && (Op.ofBits 11 52).hasRules && (Op.ofBits 1 0).hasRules
#guard (Op.sitofp 32 8 23).hasRules && (Op.uitofp 128 5 10).hasRules && (Op.sitofp 1 1 0).hasRules
#guard (Op.fpext 8 23 11 52).hasRules && (Op.fptrunc 11 52 8 23).hasRules && (Op.fpext 1 0 1 0).hasRules
#guard (Op.ptradd 0 64).hasRules && (Op.ptradd 1 1).hasRules && (Op.ptradd 0 0).hasRules
#guard (Op.fptosi 8 23 32).hasRules && (Op.fptoui 5 10 128).hasRules && (Op.fptosi 1 0 1).hasRules
#guard (Op.br).hasRules && (Op.condBr).hasRules && (Op.unreachable).hasRules &&
  (Op.call "f" [.int 8] [.int 8]).hasRules &&
  (Op.call "f" [] [.ptr 0]).hasRules
#guard ((Op.call "f" [.int 8] [.int 8]).denote? (m := SetM)).isNone
#guard ((Op.alloca .stack (.int 32) 4 none 0).denote? (m := SetM)).isNone &&
  (Op.alloca .stack (.int 32) 4 none 0).hasRules

/-- The core dialect's semantics in a monad `m` from two tables of rules,
`den` for the ops that are not terminators and `ex` for the terminators:
each op's rule, and `z p` for an op `p` that a table gives none. -/
@[instance_reducible] def denoteWith
    (den : (op : Op) → Option (HVector toType (Fir.sig (d := CoreDialect) op) →
      m (HVector toType (Fir.returnTypes (d := CoreDialect) op))))
    (ex : (op : Op) → Option (HVector toType (Fir.sig (d := CoreDialect) op) → m Exit))
    (z : {α : Type} → Op → m α) : DialectDenote CoreDialect m where
  denote op args := match den op with
    | some rule => rule args
    | none => z op
  exit op args := match ex op with
    | some rule => rule args
    | none => z op

/-- The core dialect's semantics in a monad `m` with choice and UB: each
op's rule in `Op.denote?` or `Op.exit?`, and `z p` for an op `p` that has
none, as `call`, whose `denote` no run reaches. -/
@[reducible] def denoteIn [MonadChoice m] [MonadUB m] (z : {α : Type} → Op → m α) :
    DialectDenote CoreDialect m :=
  denoteWith (fun op => op.denote?) (fun op => op.exit?) z

end Fir.Core

namespace Fir

/-- The core dialect's semantics in the set monad: each op's rule, and no
outcome where `Op.denote?` or `Op.exit?` gives none. -/
instance : DialectDenote CoreDialect SetM := Core.denoteIn fun _ _ => False

/-- The core ops that call a function: `call @g` calls `@g`. -/
instance : DialectCall CoreDialect := ⟨Core.Op.callTarget?⟩

end Fir
