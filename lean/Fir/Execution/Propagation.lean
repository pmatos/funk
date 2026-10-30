import Fir.Execution.Behaviour

/-!
# Poison classes

A poison operand gives a poison result, unless the op says otherwise
(ADR-2026-10-30-0818). That rule is a property that each op must have, so it
is checked, not only stated. Every op of every dialect declares its _poison
class_ through the class `DialectPoison` (G0):

* `propagates`: when any operand is poison, every result the op can return
  is poison. The op may still end in immediate UB by its own rules, as a
  division by a poison divisor does. UB allows anything, so it never makes
  a poison operand look like a defined value.
* `exception`: the op states its own rule for poison operands, in its prose
  and in its execution rules. `select` and `freeze` are exceptions, and so
  are the ops that only pass values on: terminators, which pass them to
  block arguments or return them, and calls.

An op that propagates poison carries a proof obligation, `PropagatesPoison`,
stated over its semantics in the set monad: every result vector that it
returns, from an operand vector that holds a poison, holds only poison. A
dialect meets the obligations of all its propagating ops by giving an
instance of `LawfulDialectPoison`. A value that cannot be poison, such as a
value of a dialect type with no poison, never triggers the obligation.
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

variable {d : Dialect} [TyDenote d.Ty] [TyPoison d.Ty] [DialectSignature d]

/-- The obligation of an op that propagates poison: from operands of which
one is poison, every result vector it returns is all poison. -/
def PropagatesPoison [DialectDenote d SetM] (op : d.Op) : Prop :=
  ∀ args : HVector toType (sig op), args.Any TyPoison.IsPoison →
    ∀ rs, DialectDenote.denote (m := SetM) op args (.ok rs) → rs.All TyPoison.IsPoison

/-- A dialect whose propagating ops do propagate poison. -/
class LawfulDialectPoison (d : Dialect) [TyDenote d.Ty] [TyPoison d.Ty] [DialectSignature d]
    [DialectPoison d] [DialectDenote d SetM] : Prop where
  propagates : ∀ op : d.Op, poisonClass op = .propagates → PropagatesPoison op

end Fir
