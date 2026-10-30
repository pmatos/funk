import Fir.Execution.Behaviour

/-!
# Poison classes

A poison operand gives a poison result, unless the op says otherwise
(ADR-2026-10-30-0818). That rule is a property that each op must have, so it
is checked, not only stated. Every op of every dialect declares its _poison
class_ through the class `DialectPoison` (G0):

* `propagates`: when any operand is poison, every result the op returns is
  poison, and the op hits immediate UB only by its own rules.
* `exception`: the op states its own rule for poison operands, in its prose
  and in its execution rules. `select` and `freeze` are exceptions, and so
  are the ops that only pass values on: terminators, which pass them to
  block arguments or return them, and calls.

An op that propagates poison carries a proof obligation, `PropagatesPoison`,
stated over its semantics in the set monad. It has two clauses:

* _Poison out._ From an operand vector that holds a poison, every result
  vector the op returns holds only poison.
* _UB only by the op's own rules._ If the op may hit UB on an operand vector
  that holds a poison, it may also hit UB on some operand vector that puts a
  defined value in place of each poison and agrees with it everywhere else.

The second clause is LLVM's principle for poison and UB (LangRef, "Poison
Values"; Alive2 agrees): a poison operand is immediate UB wherever some value
it could take would be. It allows UB on a poison divisor, since the divisor
could be zero, and on a poison dividend of `sdiv` or `srem` by `-1`, since
the dividend could be the signed minimum. It rejects UB on a poison operand
of every other propagating op: an `add` that is UB on a poison operand does
not meet it. A value that cannot be poison, such as a value of a dialect
type with no poison, never triggers either clause.
-/

namespace Fir

/-- How an op treats poison operands. -/
inductive PoisonClass where
  /-- A poison operand makes every result the op returns poison. -/
  | propagates
  /-- The op states its own rule for poison operands. -/
  | exception
  deriving Repr, DecidableEq

/-- Which values of a dialect's types are poison. -/
class TyPoison (Ty : Type) [TyDenote Ty] where
  IsPoison : {t : Ty} → ⟦t⟧ → Prop

/-- Each op of a dialect declares its poison class. -/
class DialectPoison (d : Dialect) where
  poisonClass : d.Op → PoisonClass
export DialectPoison (poisonClass)

/-- Some element of the vector has the property. -/
def HVector.Any {f : α → Type} (p : {a : α} → f a → Prop) : {as : List α} → HVector f as → Prop
  | _, .nil => False
  | _, .cons x xs => p x ∨ HVector.Any p xs

/-- Every element of the vector has the property. -/
def HVector.All {f : α → Type} (p : {a : α} → f a → Prop) : {as : List α} → HVector f as → Prop
  | _, .nil => True
  | _, .cons x xs => p x ∧ HVector.All p xs

/-- Two vectors of the same types are related position by position. -/
def HVector.Forall₂ {f : α → Type} (r : {a : α} → f a → f a → Prop) :
    {as : List α} → HVector f as → HVector f as → Prop
  | _, .nil, .nil => True
  | _, .cons x xs, .cons y ys => r x y ∧ HVector.Forall₂ r xs ys

/-- A relation that holds of every element with itself holds of every
vector with itself. -/
theorem HVector.forall₂_refl {f : α → Type} {r : {a : α} → f a → f a → Prop}
    (h : ∀ {a : α} (x : f a), r x x) : ∀ {as : List α} (xs : HVector f as), xs.Forall₂ r xs
  | _, .nil => trivial
  | _, .cons x xs => ⟨h x, HVector.forall₂_refl h xs⟩

variable {d : Dialect} [TyDenote d.Ty] [TyPoison d.Ty] [DialectSignature d]

/-- `args'` puts a defined value in place of each poison of `args`: it holds
no poison, and it agrees with `args` wherever `args` is not poison. -/
def HVector.IsFilledBy {ts : List d.Ty} (args args' : HVector toType ts) : Prop :=
  ¬ args'.Any TyPoison.IsPoison ∧ args.Forall₂ (fun x y => TyPoison.IsPoison x ∨ x = y) args'

variable [DialectDenote d SetM]

/-- Poison out: from operands of which one is poison, every result vector
the op returns is all poison. -/
def PoisonOut (op : d.Op) : Prop :=
  ∀ args : HVector toType (sig op), args.Any TyPoison.IsPoison →
    ∀ rs, DialectDenote.denote (m := SetM) op args (.ok rs) → rs.All TyPoison.IsPoison

/-- UB only by the op's own rules: if the op may hit UB on operands of which
one is poison, it may hit UB on some operands that fill each poison with a
defined value. -/
def UBByOwnRules (op : d.Op) : Prop :=
  ∀ (args : HVector toType (sig op)) (r : String), args.Any TyPoison.IsPoison →
    DialectDenote.denote (m := SetM) op args (.ub r) →
    ∃ args', args.IsFilledBy args' ∧ ∃ r', DialectDenote.denote (m := SetM) op args' (.ub r')

/-- The obligation of an op that propagates poison. -/
structure PropagatesPoison (op : d.Op) : Prop where
  /-- A poison operand gives only poison results. -/
  poisonOut : PoisonOut op
  /-- A poison operand is UB only where a defined value in its place may be. -/
  ubByOwnRules : UBByOwnRules op

/-!
# Obligations of every op

Two more obligations hold for every op, whatever its poison class.

* _Totality_ (`OpTotal`). On every operand vector, the op has some outcome:
  a result or UB. So does the exit of a terminator. An op whose semantics
  maps a case to the empty set would drop that path from every run that
  reaches it, and a run with fewer outcomes refines more sources.
* _Monotonicity_ (`OpMonotone`). Refining the operands refines what the op
  does. If each operand of `args'` refines the one of `args`, a poison
  being refined by any value, then every way the op may end on `args'` is
  allowed by some way it may end on `args`. As for behaviours, UB allows
  anything, and a result vector is allowed by one that it refines position
  by position. Where a terminator goes refines only by being the same.

Monotonicity is what makes refinement compositional. A run only passes
values from op to op, so when every op is monotone, a run on refined values
refines the run on the original ones. A pass that replaces one part of a
function with a part that refines it, such as an op's result with a value
that refines it or a callee with a function that refines it, then refines
the whole function, and its proof need only look at the part it changes.
This is also why a function refines another only if it does so on every
argument vector, poison included: a caller may pass poison. And it explains
the division rule: if `sdiv` by `-1` gave poison for a poison dividend, then
refining that poison to the signed minimum would turn a result into UB,
which is not a refinement.

Monotonicity uses the dialect's refinement of values, and the obligations
tie it to poison: a poison value is refined by every value of its type.

A dialect meets every obligation of this section by giving an instance of
`LawfulDialectPoison`.
-/

/-- One way to end allows another: UB allows anything, and a result allows
the results that refine it by `r`. -/
def Ev.IsRefinedBy (r : α → α → Prop) : Ev α → Ev α → Prop
  | .ub _, _ => True
  | .ok a, .ok b => r a b
  | .ok _, .ub _ => False

/-- A computation is refined by another when every way the second may end is
allowed by some way the first may end. -/
def SetM.IsRefinedBy (r : α → α → Prop) (s t : SetM α) : Prop :=
  ∀ e, t e → ∃ e', s e' ∧ Ev.IsRefinedBy r e' e

/-- A computation refines itself when `r` is reflexive. -/
theorem SetM.isRefinedBy_refl {r : α → α → Prop} (h : ∀ a, r a a) (s : SetM α) :
    SetM.IsRefinedBy r s s := fun e he =>
  ⟨e, he, match e with
    | .ok a => h a
    | .ub _ => trivial⟩

/-- Totality: on every operand vector the op has an outcome, and so does the
exit of a terminator. -/
def OpTotal (op : d.Op) : Prop :=
  ∀ args : HVector toType (sig op), (∃ e, DialectDenote.denote (m := SetM) op args e) ∧
    (isTerminator op = true → ∃ e, DialectDenote.exit (m := SetM) op args e)

variable [TyRefinement d.Ty]

/-- Monotonicity: on operands that refine `args` position by position, every
way the op may end is allowed by a way it may end on `args`. -/
def OpMonotone (op : d.Op) : Prop :=
  ∀ args args' : HVector toType (sig op), args.Forall₂ TyRefinement.IsRefinedBy args' →
    SetM.IsRefinedBy (HVector.Forall₂ TyRefinement.IsRefinedBy)
        (DialectDenote.denote op args) (DialectDenote.denote op args') ∧
      SetM.IsRefinedBy Eq (DialectDenote.exit op args) (DialectDenote.exit op args')

/-- A dialect whose ops meet the poison obligations: a poison value is
refined by every value of its type, every propagating op propagates poison,
and every op is total and monotone. -/
class LawfulDialectPoison (d : Dialect) [TyDenote d.Ty] [TyPoison d.Ty] [TyRefinement d.Ty]
    [DialectSignature d] [DialectPoison d] [DialectDenote d SetM] : Prop where
  poison_isRefinedBy : ∀ {t : d.Ty} (p v : ⟦t⟧), TyPoison.IsPoison p → TyRefinement.IsRefinedBy p v
  propagates : ∀ op : d.Op, poisonClass op = .propagates → PropagatesPoison op
  total : ∀ op : d.Op, OpTotal op
  monotone : ∀ op : d.Op, OpMonotone op

end Fir
