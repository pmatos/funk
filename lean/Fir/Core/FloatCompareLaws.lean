import Fir.Core.Semantics
import Fir.Core.Poison

/-!
# Float comparison is lawful

`fcmp`, with each of its fourteen predicates and at every format, meets the
obligations of the poison classes section, as `icmp` does. It propagates
poison (ADR-2026-10-29-2006), so it meets both poison clauses, returns a
result on some operands with no poison, and is total and monotone.

It is never UB: it has one outcome, a result, on every operand vector, so
it is total, and the clause "UB only by the op's own rules" holds at once.
It returns a result on the defined operands `+0` and `+0`. It is monotone
because a poison operand gives a poison result, which every result
refines, and defined operands are refined only by themselves. None of this
looks at how the model compares: the proofs hold for any comparison of
bit patterns.
-/

namespace Fir.Core

/-- A poison operand of `fcmp` gives a poison `i1`. -/
theorem fcmpValues_poison (p : FPred) {a b : PoisonOr (BitVec (floatWidth e m))}
    (h : a = .poison ∨ b = .poison) : fcmpValues p a b = .poison := by
  rcases h with rfl | rfl
  · rfl
  · cases a <;> rfl

/-- `fcmp` on operands that refine others gives an `i1` that refines
theirs. -/
theorem fcmpValues_isRefinedBy (p : FPred) {a b a' b' : PoisonOr (BitVec (floatWidth e m))}
    (ha : a ⊑ a') (hb : b ⊑ b') : fcmpValues p a b ⊑ fcmpValues p a' b' := by
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

/-- `fcmp` propagates poison, with every predicate: a poison operand gives
only a poison `i1`, and it is never UB. -/
theorem fcmp_propagatesPoison (p : FPred) (e m : Nat) :
    PropagatesPoison (d := CoreDialect) (.fcmp p e m) where
  poisonOut
    | .cons _ (.cons _ .nil), h, _, hrs => by
      cases hrs
      exact ⟨fcmpValues_poison p (h.imp_right fun h => h.elim id False.elim), trivial⟩
  ubByOwnRules
    | .cons _ (.cons _ .nil), _, _, hub => nomatch hub

/-- `fcmp` returns a result on two defined operands, with every
predicate. -/
theorem fcmp_returnsOnDefined (p : FPred) (e m : Nat) :
    ReturnsOnDefined (d := CoreDialect) (.fcmp p e m) := by
  refine ⟨.cons (.value 0) (.cons (.value 0) .nil), ?_, _, rfl⟩
  rintro (h | h | h) <;> cases h

/-- `fcmp` has an outcome on every operand vector, with every predicate. -/
theorem fcmp_total (p : FPred) (e m : Nat) : OpTotal (d := CoreDialect) (.fcmp p e m) := fun
  | .cons _ (.cons _ .nil) => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `fcmp` is monotone, with every predicate. -/
theorem fcmp_monotone (p : FPred) (e m : Nat) : OpMonotone (d := CoreDialect) (.fcmp p e m) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a (.cons b .nil), .cons a' (.cons b' .nil), ⟨ha, hb, _⟩ =>
    intro r hr
    cases hr
    exact ⟨_, rfl, fcmpValues_isRefinedBy p ha hb, trivial⟩

end Fir.Core
