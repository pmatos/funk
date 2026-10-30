import Fir.Core.Semantics
import Fir.Core.Poison

/-!
# Freeze is lawful

`freeze` is an exception to poison propagation (ADR-2026-10-30-0818), so of
the obligations of the poison classes section it meets two: it is total
and monotone. In the set monad, `freeze` of a value gives that value, and
`freeze` of poison gives every value of its type, each as one way the op
may end. So it has an outcome on every operand, and it never gives poison.

It is monotone because a poison operand allows every value: whatever value
`freeze` gives on an operand that refines poison, `freeze` of the poison
may give it too. A defined operand is refined only by itself.
-/

namespace Fir.Core

/-- In the set monad, `freeze` of `a` gives the bits `b` exactly when `a` is
poison or is `b`, and it never hits UB. -/
theorem freeze_denote (w : Nat) (a : PoisonOr (BitVec w))
    (e : Ev (HVector toType (Fir.returnTypes (d := CoreDialect) (.freeze w)))) :
    DialectDenote.denote (m := SetM) (d := CoreDialect) (.freeze w) (.cons a .nil) e ↔
      ∃ b, e = .ok (.cons (.value b) .nil) ∧ (a = .poison ∨ a = .value b) := by
  cases a with
  | value x =>
    constructor
    · rintro (⟨v, hv, rfl⟩ | ⟨_, hr, _⟩)
      · cases hv
        exact ⟨x, rfl, .inr rfl⟩
      · cases hr
    · rintro ⟨b, rfl, h | h⟩
      · cases h
      · cases h
        exact .inl ⟨_, rfl, rfl⟩
  | poison =>
    constructor
    · rintro (⟨v, (⟨b, _, hv⟩ | ⟨_, ⟨_, hr⟩, _⟩), rfl⟩ | ⟨_, (⟨_, _, hr⟩ | ⟨_, ⟨_, hr⟩, _⟩), _⟩)
      · cases hv
        exact ⟨b, rfl, .inl rfl⟩
      all_goals cases hr
    · rintro ⟨b, rfl, _⟩
      exact .inl ⟨_, .inl ⟨b, ⟨b, rfl⟩, rfl⟩, rfl⟩

/-- `freeze` has an outcome on every operand: the operand's value, or any
bits when it is poison. -/
theorem freeze_total (w : Nat) : OpTotal (d := CoreDialect) (.freeze w) := fun
  | .cons a .nil => ⟨fun _ => match a with
      | .value x => ⟨_, (freeze_denote w _ _).2 ⟨x, rfl, .inr rfl⟩⟩
      | .poison => ⟨_, (freeze_denote w _ _).2 ⟨0, rfl, .inl rfl⟩⟩,
    fun h => nomatch h⟩

/-- `freeze` is monotone: each value it may give on an operand that refines
another, it may give on that other. -/
theorem freeze_monotone (w : Nat) : OpMonotone (d := CoreDialect) (.freeze w) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a .nil, .cons a' .nil, ⟨ha, _⟩ =>
    intro e he
    obtain ⟨b, rfl, hb⟩ := (freeze_denote w a' e).1 he
    refine ⟨_, (freeze_denote w a _).2 ⟨b, rfl, ?_⟩,
      HVector.forall₂_refl Core.Ty.isRefinedBy_refl _⟩
    cases a with
    | poison => exact .inl rfl
    | value x =>
      cases a' with
      | poison => exact ha.elim
      | value x' =>
        have hx : x = x' := ha
        subst hx
        rcases hb with h | h
        · cases h
        · exact .inr h

end Fir.Core
