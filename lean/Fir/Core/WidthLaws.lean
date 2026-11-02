import Fir.Core.Semantics
import Fir.Core.Poison

/-!
# Width changes are lawful

`zext`, `sext` and `trunc` meet the obligations of the poison classes
section, at every pair of widths. They propagate poison
(ADR-2026-10-30-0818), so each meets both poison clauses, returns a result
on an operand that is not poison, and is total and monotone.

None of them is ever UB, so the clause "UB only by the op's own rules"
holds at once. Each is monotone because a poison operand gives a poison
result, which every result refines, and a defined operand is refined only
by itself. The proofs rest on two facts of any rule on one value that
gives poison on poison, as these three do: it gives poison there, and so
it is monotone.
-/

namespace Fir.Core

/-- A rule from values of `iM` to values of `iN` gives poison on poison. -/
def UnaryStrict (g : PoisonOr (BitVec m) → PoisonOr (BitVec n)) : Prop :=
  g .poison = .poison

/-- A rule that gives poison on poison gives, on an operand that refines
another, a result that refines the other's. -/
theorem UnaryStrict.isRefinedBy {g : PoisonOr (BitVec m) → PoisonOr (BitVec n)}
    (hg : UnaryStrict g) {a a' : PoisonOr (BitVec m)} (ha : a ⊑ a') : g a ⊑ g a' := by
  cases a with
  | poison => rw [hg]; trivial
  | value x =>
    cases a' with
    | poison => exact ha.elim
    | value x' =>
      have hx : x = x' := ha
      subst hx
      exact PoisonOr.isRefinedBy_refl _

theorem unaryStrict_zextValue (n : Nat) : UnaryStrict (m := m) (zextValue n) := rfl

theorem unaryStrict_sextValue (n : Nat) : UnaryStrict (m := m) (sextValue n) := rfl

theorem unaryStrict_truncValue (n : Nat) : UnaryStrict (m := m) (truncValue n) := rfl

/-! # `zext` -/

/-- `zext` propagates poison, at every pair of widths: a poison operand
gives only poison, and it is never UB. -/
theorem zext_propagatesPoison (m n : Nat) : PropagatesPoison (d := CoreDialect) (.zext m n) where
  poisonOut
    | .cons a .nil, h, _, hrs => by
      cases hrs
      obtain rfl : a = .poison := h.elim id False.elim
      exact ⟨rfl, trivial⟩
  ubByOwnRules
    | .cons _ .nil, _, _, hub => nomatch hub

/-- `zext` returns a result on a defined operand, at every pair of
widths. -/
theorem zext_returnsOnDefined (m n : Nat) : ReturnsOnDefined (d := CoreDialect) (.zext m n) := by
  refine ⟨.cons (.value 0) .nil, ?_, _, rfl⟩
  rintro (h | h) <;> cases h

/-- `zext` has an outcome on every operand, at every pair of widths. -/
theorem zext_total (m n : Nat) : OpTotal (d := CoreDialect) (.zext m n) := fun
  | .cons _ .nil => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `zext` is monotone, at every pair of widths. -/
theorem zext_monotone (m n : Nat) : OpMonotone (d := CoreDialect) (.zext m n) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a .nil, .cons a' .nil, ⟨ha, _⟩ =>
    intro e he
    cases he
    exact ⟨_, rfl, (unaryStrict_zextValue n).isRefinedBy ha, trivial⟩

/-! # `sext` -/

/-- `sext` propagates poison, at every pair of widths. -/
theorem sext_propagatesPoison (m n : Nat) : PropagatesPoison (d := CoreDialect) (.sext m n) where
  poisonOut
    | .cons a .nil, h, _, hrs => by
      cases hrs
      obtain rfl : a = .poison := h.elim id False.elim
      exact ⟨rfl, trivial⟩
  ubByOwnRules
    | .cons _ .nil, _, _, hub => nomatch hub

/-- `sext` returns a result on a defined operand, at every pair of
widths. -/
theorem sext_returnsOnDefined (m n : Nat) : ReturnsOnDefined (d := CoreDialect) (.sext m n) := by
  refine ⟨.cons (.value 0) .nil, ?_, _, rfl⟩
  rintro (h | h) <;> cases h

/-- `sext` has an outcome on every operand, at every pair of widths. -/
theorem sext_total (m n : Nat) : OpTotal (d := CoreDialect) (.sext m n) := fun
  | .cons _ .nil => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `sext` is monotone, at every pair of widths. -/
theorem sext_monotone (m n : Nat) : OpMonotone (d := CoreDialect) (.sext m n) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a .nil, .cons a' .nil, ⟨ha, _⟩ =>
    intro e he
    cases he
    exact ⟨_, rfl, (unaryStrict_sextValue n).isRefinedBy ha, trivial⟩

/-! # `trunc` -/

/-- `trunc` propagates poison, at every pair of widths. -/
theorem trunc_propagatesPoison (m n : Nat) :
    PropagatesPoison (d := CoreDialect) (.trunc m n) where
  poisonOut
    | .cons a .nil, h, _, hrs => by
      cases hrs
      obtain rfl : a = .poison := h.elim id False.elim
      exact ⟨rfl, trivial⟩
  ubByOwnRules
    | .cons _ .nil, _, _, hub => nomatch hub

/-- `trunc` returns a result on a defined operand, at every pair of
widths. -/
theorem trunc_returnsOnDefined (m n : Nat) :
    ReturnsOnDefined (d := CoreDialect) (.trunc m n) := by
  refine ⟨.cons (.value 0) .nil, ?_, _, rfl⟩
  rintro (h | h) <;> cases h

/-- `trunc` has an outcome on every operand, at every pair of widths. -/
theorem trunc_total (m n : Nat) : OpTotal (d := CoreDialect) (.trunc m n) := fun
  | .cons _ .nil => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `trunc` is monotone, at every pair of widths. -/
theorem trunc_monotone (m n : Nat) : OpMonotone (d := CoreDialect) (.trunc m n) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a .nil, .cons a' .nil, ⟨ha, _⟩ =>
    intro e he
    cases he
    exact ⟨_, rfl, (unaryStrict_truncValue n).isRefinedBy ha, trivial⟩

end Fir.Core
