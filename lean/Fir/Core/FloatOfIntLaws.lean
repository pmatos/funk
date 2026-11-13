import Fir.Core.FloatArithLaws
import Fir.Core.FloatOfInt

/-!
# Conversions from integers to floats are lawful

`sitofp` and `uitofp`, from every width to every format, meet the
obligations of the poison classes section. Each propagates poison
(ADR-2026-10-29-2006), so it meets both poison clauses, returns a result
on an operand that is not poison, and is total and monotone. Each also
meets the effect obligations of a pure op (ADR-2026-11-09-1549): it is
never UB, and on an operand that is not poison it gives a defined result.

The proofs are those of the float arithmetic of one operand, whose
operand is a float where these take an integer: the rule gives a float
result of the model on a value, which has a way to end, is never UB and
is defined bits, and poison on poison. None of this looks at what the
model computes, so the proofs hold at every format, valid or not.
-/

namespace Fir.Core

/-- The rule of `sitofp` and `uitofp` has a way to end, and is never UB. -/
theorem intToFloat_ends (e m : Nat) (signed : Bool) (a : PoisonOr (BitVec n)) :
    Ends (intToFloat (μ := SetM) e m signed a) := by
  cases a <;> first | exact pure_ends _ | (dsimp only [intToFloat]; exact floatResult_ends e m _)

/-- A morphism that keeps choice and UB maps the rule of `sitofp` and
`uitofp` in one monad to their rule in the other. -/
theorem intToFloat_map {μ ν : Type → Type} [Monad μ] [Monad ν] [MonadChoice μ] [MonadChoice ν]
    [MonadUB μ] [MonadUB ν] (φ : MonadMorphism μ ν) (hk : φ.KeepsChoiceUB) (e m : Nat)
    (signed : Bool) (a : PoisonOr (BitVec n)) :
    φ.map (intToFloat (μ := μ) e m signed a) = intToFloat e m signed a := by
  cases a <;> first | exact φ.map_pure _ | (dsimp only [intToFloat]; exact floatResult_map φ hk _)

section
variable (n e m : Nat)

/-- The op instance of `sitofp`, with `signed`, or of `uitofp`, from `iN`
to `float<e,m>`. -/
def intToFloatOp : Bool → Op
  | true => .sitofp n e m
  | false => .uitofp n e m

/-- `sitofp` and `uitofp` propagate poison: a poison operand gives only a
poison result, and they are never UB. -/
theorem intToFloat_propagatesPoison (signed : Bool) :
    PropagatesPoison (d := CoreDialect) (intToFloatOp n e m signed) := by
  cases signed <;> exact {
    poisonOut := fun
      | .cons a .nil, h, _, hrs => by
        have hp : a = .poison := h.elim id False.elim
        subst hp
        obtain ⟨v, hv, h⟩ := oneFloat_ok (intToFloat_ends e m _ _) hrs
        cases hv
        cases h
        exact ⟨rfl, trivial⟩
    ubByOwnRules := fun
      | .cons a .nil, r, _, hub => absurd hub (oneFloat_not_ub (intToFloat_ends e m _ a) r) }

/-- `sitofp` and `uitofp` return a result on a defined operand. -/
theorem intToFloat_returnsOnDefined (signed : Bool) :
    ReturnsOnDefined (d := CoreDialect) (intToFloatOp n e m signed) := by
  obtain ⟨v, hv⟩ := (intToFloat_ends (n := n) e m signed (.value 0)).some
  cases signed <;>
  · refine ⟨.cons (.value 0) .nil, ?_, _, oneFloat_of hv⟩
    rintro (h | h) <;> cases h

/-- `sitofp` and `uitofp` have an outcome on every operand. -/
theorem intToFloat_total (signed : Bool) :
    OpTotal (d := CoreDialect) (intToFloatOp n e m signed) := by
  cases signed <;> exact fun
    | .cons a .nil =>
      ⟨fun _ => by
        obtain ⟨_, hv⟩ := (intToFloat_ends e m _ a).some
        exact ⟨_, oneFloat_of hv⟩, fun h => nomatch h⟩

/-- `sitofp` and `uitofp` are monotone. -/
theorem intToFloat_monotone (signed : Bool) :
    OpMonotone (d := CoreDialect) (intToFloatOp n e m signed) := by
  cases signed <;>
  · intro args args' h
    refine ⟨fun _ => ?_, fun h => nomatch h⟩
    match args, args', h with
    | .cons a .nil, .cons a' .nil, ⟨ha, _⟩ =>
      cases a with
      | poison => exact oneFloat_poison_isRefinedBy (intToFloat_ends e m _ a')
      | value x =>
        cases a' with
        | poison => exact ha.elim
        | value x' =>
          have hx : x = x' := ha
          subst hx
          exact SetM.isRefinedBy_refl (HVector.forall₂_refl Core.Ty.isRefinedBy_refl) _

/-- `sitofp` and `uitofp` are never UB. -/
theorem intToFloat_neverUB (signed : Bool) :
    NeverUBSetM (d := CoreDialect) (intToFloatOp n e m signed) := by
  cases signed <;> exact fun
    | .cons a .nil, r => ⟨fun _ => oneFloat_not_ub (intToFloat_ends e m _ a) r, fun h => nomatch h⟩

/-- On a defined operand, `sitofp` and `uitofp` give a defined result. -/
theorem intToFloat_makesNoPoison (signed : Bool) :
    MakesNoPoisonSetM (d := CoreDialect) (intToFloatOp n e m signed) := by
  cases signed <;> exact fun _ args hd rs hr => match args, hd, hr with
    | .cons a .nil, hd, hr => by
      cases a with
      | poison => exact absurd (.inl rfl) hd
      | value x =>
        obtain ⟨v, hv, ⟨⟩⟩ := oneFloat_ok (intToFloat_ends e m _ _) hr
        obtain ⟨_, h⟩ := floatResult_defined e m _ _ (by dsimp only [intToFloat] at hv; exact hv)
        cases h
        exact oneFloat_defined

end

end Fir.Core
