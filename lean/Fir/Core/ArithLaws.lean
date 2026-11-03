import Fir.Core.Semantics
import Fir.Core.Poison

/-!
# Constants are lawful

`const` meets the obligations of the poison classes section, for the core
dialect's semantics. It propagates poison (ADR-2026-10-30-0818), so it meets
the poison clauses, returns a result on some operands with no poison, and is
total and monotone. `const` meets its poison clauses and is monotone whatever
its semantics, as the core poison classes section proves; its rule gives the
rest.

`poison` meets them the same way (ADR-2026-11-03-1615). Its one operand
vector is the empty one, which holds no poison, and on it `poison` returns
its result, the poison of its type: a result on defined operands, which is
all that obligation asks, and an outcome, which is all that totality asks.

The sum without flags gives poison on a poison operand, and on operands
that refine others it gives a sum that refines theirs. The next section
proves `add`, with and without its flags, lawful, with `sub` and `mul`.
-/

namespace Fir.Core

/-- `const` returns its value on its one operand vector, the empty one. -/
theorem const_returnsOnDefined (w : Nat) (v : BitVec w) :
    ReturnsOnDefined (d := CoreDialect) (.const w v) :=
  ⟨.nil, fun h => h, _, rfl⟩

/-- `const` has an outcome on its one operand vector. -/
theorem const_total (w : Nat) (v : BitVec w) : OpTotal (d := CoreDialect) (.const w v) :=
  fun _ => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `poison` returns its result on its one operand vector, the empty one,
which holds no poison. -/
theorem poison_returnsOnDefined (w : Nat) : ReturnsOnDefined (d := CoreDialect) (.poison w) :=
  ⟨.nil, fun h => h, _, rfl⟩

/-- `poison` has an outcome on its one operand vector. -/
theorem poison_total (w : Nat) : OpTotal (d := CoreDialect) (.poison w) :=
  fun _ => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- In the set monad, `poison` returns the poison of its type, and nothing
else: no other value and no UB. -/
theorem poison_denote (w : Nat)
    (e : Ev (HVector toType (Fir.returnTypes (d := CoreDialect) (.poison w)))) :
    DialectDenote.denote (m := SetM) (d := CoreDialect) (.poison w) .nil e ↔
      e = .ok (.cons (PoisonOr.poison : PoisonOr (BitVec w)) .nil) :=
  Iff.rfl

/-- A poison operand of `add` gives poison. -/
theorem addValues_poison {a b : PoisonOr (BitVec w)} (h : a = .poison ∨ b = .poison) :
    addValues a b = .poison := by
  rcases h with rfl | rfl
  · rfl
  · cases a <;> rfl

/-- `add` on operands that refine others gives a sum that refines theirs. -/
theorem addValues_isRefinedBy {a b a' b' : PoisonOr (BitVec w)} (ha : a ⊑ a') (hb : b ⊑ b') :
    addValues a b ⊑ addValues a' b' := by
  cases a with
  | poison => trivial
  | value x =>
    cases b with
    | poison => trivial
    | value y =>
      cases a' with
      | poison => exact ha.elim
      | value x' =>
        cases b' with
        | poison => exact hb.elim
        | value y' =>
          have hx : x = x' := ha
          have hy : y = y' := hb
          subst hx hy
          exact PoisonOr.isRefinedBy_refl _

end Fir.Core
