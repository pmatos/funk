import Fir.Core.Arith
import Fir.Core.Wrap
import Fir.Core.Freeze
import Fir.Core.Bitwise
import Fir.Core.Width
import Fir.Core.Div
import Fir.Core.Compare
import Fir.Core.Control
import Fir.Core.Branch
import Fir.Core.Call
import Fir.Core.Text

/-!
# The core dialect's semantics

`DialectDenote CoreDialect SetM` gives every core op its meaning in the set
monad. It is one instance over all 24 core ops, which sends each op to the
rule of its family. The rules are written once, for any monad that has
the effects they ask for: `Op.denote?` for the ops that are not
terminators, and `Op.exit?` for the terminators. `freeze` asks for the
choice effect, and the divisions and `cond_br` for the UB effect. So this
instance and the tree of choices that `fir-ref run` computes in share
them.

# Ops without rules

An op whose family has not landed has no rule yet: `Op.denote?` or
`Op.exit?` gives `none` for it. Since #20 named the callee of `call`,
every core op has its rules, so none is left without. `call`'s meaning is
its callee's run, so `Op.denote?` gives `none` for it too, and it is not
an op without rules (the section on calls below). ADR-2026-10-30-1855
decides what an op without rules does until its family lands, and the
spec keeps that rule for every dialect:

* In the spec, it has no outcome: on every operand vector, its `denote` or
  its `exit` is the empty set. That is not a stand-in semantics. The
  totality obligation `OpTotal` rejects it, as it rejects
  `Core.Unlawful.noOutcome`, so `LawfulDialectPoison CoreDialect` cannot be
  proved while any op lacks its rules.
* Only totality, `ReturnsOnDefined`, progress and the lawful class reject
  it. `PropagatesPoison` and `OpMonotone` hold of such an op, and
  `NeverStuck` and `FuelMonotone` of a function that reaches one, since the
  empty set meets every bound on what may happen; and such a function
  refines every source. So none of these statements is claimed of an op,
  or of a function that reaches one, before the op has rules. The general
  theorems `Func.fuelMonotone`, `Func.neverStuck` and
  `Func.neverStuck_of_local` cover such a function too, but only vacuously
  on the paths that reach the op: they say nothing of how it behaves.
* A run that reaches such an op has no way to end on that path; when
  every path does, `Progress` fails. So `Progress` and `NeverStuck` were
  proved first for every valid core function without a `call` op, while
  `call` had no rules (`Core.callFree_progress`, `Core.callFree_neverStuck`),
  and are proved now for every function of every valid core module, calls
  and recursion included (`Core.progress`, `Core.neverStuck`).
* `fir-ref run` prints no outcome for a run that reaches such an op. It
  says that the op has no execution rules yet, as an error
  (ADR-2026-10-30-1856).

Each ticket from #14 to #19 adds its family's rules to `Op.denote?` and
`Op.exit?`, in its own section, and proves their obligations beside them.
#20 names the callee of `call` instead, below.

# Calls

`call` takes its meaning from the call effect, which the interpreter runs
(ADR-2026-11-02-0836), not from `denote`. The instance
`DialectCall CoreDialect` says which core ops call a function: `call @g`
calls `@g` (`Core.Op.callTarget?`, in the section on calls). The interpreter
runs the callee of every op that has one before it looks at `denote`, so
`call` has no rule here: `Op.denote?` gives `none` for it, and in the set
monad its `denote` has no outcome, which no run reaches. It has no
op-level obligation either: the poison obligations ask totality and
monotonicity only of terminators and of ops with no callee
(ADR-2026-11-02-1514). `Op.hasRules` counts `call` as an op with rules,
since its callee's run is its meaning.
-/

namespace Fir.Core

variable {m : Type → Type} [Monad m]

/-- The rule of each core op that is not a terminator, in any monad with
the choice and UB effects, when its family has given it one. -/
def Op.denote? [MonadChoice m] [MonadUB m] : (op : Op) →
    Option (HVector toType (Fir.sig (d := CoreDialect) op) →
      m (HVector toType (Fir.returnTypes (d := CoreDialect) op)))
  | .const w v => some fun _ => pure (.cons (constValue w v) .nil)
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
  | .select _ => some fun
    | .cons c (.cons a (.cons b .nil)) => pure (.cons (selectValues c a b) .nil)
  | .zext _ n => some fun
    | .cons a .nil => pure (.cons (zextValue n a) .nil)
  | .sext _ n => some fun
    | .cons a .nil => pure (.cons (sextValue n a) .nil)
  | .trunc _ n => some fun
    | .cons a .nil => pure (.cons (truncValue n a) .nil)
  | _ => none

/-- The rule of each core terminator, in any monad with the UB effect, when
its family has given it one. -/
def Op.exit? [MonadUB m] : (op : Op) →
    Option (HVector toType (Fir.sig (d := CoreDialect) op) → m Exit)
  | .br => some fun _ => pure brExit
  | .condBr => some fun
    | .cons c .nil => exitOfEv (condBrExit c)
  | .ret _ => some fun _ => pure retExit
  | _ => none

/-- The op has rules: as an op that is not a terminator, as a terminator,
or as an op that calls a function, whose meaning is its callee's run. It
looks at the rules in the set monad, which has the effects of choice and
UB that the rules of #14, #18 and #19 ask for. -/
def Op.hasRules (op : Op) : Bool :=
  (op.denote? (m := SetM)).isSome || (op.exit? (m := SetM)).isSome || op.callTarget?.isSome

-- Every core op has rules: one instance of each, `add` with each of its
-- flags and `icmp` with each of its predicates among them. `call`'s are
-- its callee's run: it has no entry in `Op.denote?`.
#guard (samples.filter Op.hasRules).map Op.name == samples.map Op.name
#guard WrapFlags.all.all fun f => (Op.add 1 f).hasRules && (Op.sub 7 f).hasRules
#guard Pred.all.all fun p => (Op.icmp p 1).hasRules
#guard (Op.br).hasRules && (Op.condBr).hasRules && (Op.call "f" [.int 8] [.int 8]).hasRules &&
  (Op.call "f" [] [.ptr]).hasRules
#guard ((Op.call "f" [.int 8] [.int 8]).denote? (m := SetM)).isNone

end Fir.Core

namespace Fir

/-- The core dialect's semantics in the set monad: each op's rule, and no
outcome for an op that has no rule yet. -/
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
