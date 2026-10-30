import Fir.Core.Semantics
import Fir.Core.Poison

/-!
# Constants and addition are lawful

`const` and `add` without flags meet the obligations of the poison classes
section, for the core dialect's semantics. Both propagate poison
(ADR-2026-10-30-0818), so each meets the poison clauses, returns a result on
some operands with no poison, and is total and monotone. `const` meets its
poison clauses and is monotone whatever its semantics, as the core poison
classes section proves; its rule gives the rest.

`add` without flags never hits UB, so its UB clause holds at once. A poison
operand gives poison, so its results are poison too. It is monotone because
a poison operand gives a poison result, which every result refines, and
defined operands are refined only by themselves.
-/

namespace Fir.Core

/-- `const` returns its value on its one operand vector, the empty one. -/
theorem const_returnsOnDefined (w : Nat) (v : BitVec w) :
    ReturnsOnDefined (d := CoreDialect) (.const w v) :=
  ⟨.nil, fun h => h, _, rfl⟩

/-- `const` has an outcome on its one operand vector. -/
theorem const_total (w : Nat) (v : BitVec w) : OpTotal (d := CoreDialect) (.const w v) :=
  fun _ => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

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
    | poison => cases x <;> trivial
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

/-- `add` without flags propagates poison: a poison operand gives only
poison, and it is never UB. -/
theorem add_propagatesPoison (w : Nat) : PropagatesPoison (d := CoreDialect) (.add w {}) where
  poisonOut
    | .cons _ (.cons _ .nil), h, _, hrs => by
      cases hrs
      exact ⟨addValues_poison (h.imp_right fun h => h.elim id False.elim), trivial⟩
  ubByOwnRules
    | .cons _ (.cons _ .nil), _, _, hub => nomatch hub

/-- `add` without flags returns a sum on two defined operands. -/
theorem add_returnsOnDefined (w : Nat) : ReturnsOnDefined (d := CoreDialect) (.add w {}) := by
  refine ⟨.cons (.value 0) (.cons (.value 0) .nil), ?_, _, rfl⟩
  rintro (h | h | h) <;> cases h

/-- `add` without flags has an outcome on every operand vector. -/
theorem add_total (w : Nat) : OpTotal (d := CoreDialect) (.add w {}) := fun
  | .cons _ (.cons _ .nil) => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `add` without flags is monotone: on operands that refine others, its sum
refines theirs. -/
theorem add_monotone (w : Nat) : OpMonotone (d := CoreDialect) (.add w {}) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a (.cons b .nil), .cons a' (.cons b' .nil), ⟨ha, hb, _⟩ =>
    intro e he
    cases he
    exact ⟨_, rfl, addValues_isRefinedBy ha hb, trivial⟩

end Fir.Core
