import Fir.Core.Semantics
import Fir.Core.Poison
import Fir.Execution.EffectLaws

/-!
# The pointer offset is lawful

`ptradd`, at every memory and every width of its integer, meets the
obligations of the poison classes section. It propagates poison
(ADR-2026-10-29-2006), so it meets both poison clauses, returns a result
on operands with no poison, and is total and monotone. It also meets the
effect obligations of a pure op: it is never UB, and on operands with no
poison it gives a defined pointer.

Its rule gives poison when either operand is poison, and otherwise a
pointer, at once. So a poison operand gives a poison result, which every
result refines, and defined operands are refined only by themselves, so
the rule is monotone. None of this looks at the pointer or the integer, so
the proofs hold at every memory and every width, valid or not.
-/

namespace Fir.Core

open Memory

/-- The rule of `ptradd` gives poison on a poison operand. -/
theorem ptraddValue_poison {p : PoisonOr Pointer} {k : PoisonOr (BitVec w)}
    (h : p = .poison ∨ k = .poison) : ptraddValue p k = .poison := by
  rcases h with rfl | rfl
  · rfl
  · cases p <;> rfl

/-- On operands that refine others, the rule of `ptradd` gives a pointer
that refines the other's. -/
theorem ptraddValue_isRefinedBy {p p' : PoisonOr Pointer} {k k' : PoisonOr (BitVec w)}
    (hp : p ⊑ p') (hk : k ⊑ k') : ptraddValue p k ⊑ ptraddValue p' k' := by
  cases p with
  | poison => rw [ptraddValue_poison (.inl rfl)]; trivial
  | value x =>
    cases k with
    | poison => rw [ptraddValue_poison (.inr rfl)]; trivial
    | value y =>
      cases p' with
      | poison => exact hp.elim
      | value x' =>
        cases k' with
        | poison => exact hk.elim
        | value y' =>
          have hx : x = x' := hp
          have hy : y = y' := hk
          subst hx hy
          exact PoisonOr.isRefinedBy_refl _

/-- `ptradd` propagates poison: a poison operand gives only a poison
result, and it is never UB. -/
theorem ptradd_propagatesPoison (n w : Nat) :
    PropagatesPoison (d := CoreDialect) (.ptradd n w) where
  poisonOut
    | .cons _ (.cons _ .nil), h, _, hrs => by
      cases hrs
      exact ⟨ptraddValue_poison (h.imp_right fun h => h.elim id False.elim), trivial⟩
  ubByOwnRules
    | .cons _ (.cons _ .nil), _, _, hub => nomatch hub

/-- `ptradd` returns a result on a defined pointer and integer. -/
theorem ptradd_returnsOnDefined (n w : Nat) :
    ReturnsOnDefined (d := CoreDialect) (.ptradd n w) := by
  refine ⟨.cons (.value ⟨none, 0⟩) (.cons (.value 0) .nil), ?_, _, rfl⟩
  rintro (h | h | h) <;> cases h

/-- `ptradd` has an outcome on every operand vector. -/
theorem ptradd_total (n w : Nat) : OpTotal (d := CoreDialect) (.ptradd n w) := fun
  | .cons _ (.cons _ .nil) => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `ptradd` is monotone. -/
theorem ptradd_monotone (n w : Nat) : OpMonotone (d := CoreDialect) (.ptradd n w) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a (.cons b .nil), .cons a' (.cons b' .nil), ⟨ha, hb, _⟩ =>
    intro e he
    cases he
    exact ⟨_, rfl, ptraddValue_isRefinedBy ha hb, trivial⟩

/-- `ptradd` is never UB. -/
theorem ptradd_neverUB (n w : Nat) : NeverUBSetM (d := CoreDialect) (.ptradd n w) := fun
  | .cons _ (.cons _ .nil), _ => ⟨fun _ h => (by cases h), fun h => nomatch h⟩

/-- On a defined pointer and integer, `ptradd` gives a defined pointer. -/
theorem ptradd_makesNoPoison (n w : Nat) : MakesNoPoisonSetM (d := CoreDialect) (.ptradd n w) :=
  fun _ args hd _ hr => match args, hd, hr with
    | .cons p (.cons k .nil), hd, hr => by
      cases p with
      | poison => exact absurd (.inl rfl) hd
      | value x =>
        cases k with
        | poison => exact absurd (.inr (.inl rfl)) hd
        | value y =>
          cases hr
          rintro (h | h)
          · exact nomatch h
          · exact h.elim

end Fir.Core
