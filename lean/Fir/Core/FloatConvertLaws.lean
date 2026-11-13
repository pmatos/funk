import Fir.Core.FloatArithLaws
import Fir.Core.FloatConvert

/-!
# Conversions between float formats are lawful

`fpext` and `fptrunc`, between every two formats, meet the obligations of
the poison classes section. Each propagates poison (ADR-2026-10-29-2006),
so it meets both poison clauses, returns a result on an operand that is
not poison, and is total and monotone. Each also meets the effect
obligations of a pure op (ADR-2026-11-09-1549): it is never UB, and on an
operand that is not poison it gives a defined result, a NaN's included.

The proofs are those of the float arithmetic of one operand, whose result
is in the operand's format where these give one in another: the rule gives
a float result of the model on a value, which has a way to end, is never
UB and is defined bits, and poison on poison. None of this looks at what
the model computes, or at which pair of formats validation lets each op
take, so the proofs hold at every pair, valid or not.
-/

namespace Fir.Core

/-- The rule of `fpext` and `fptrunc` has a way to end, and is never UB. -/
theorem convertFloat_ends (e m e' m' : Nat) (a : PoisonOr (BitVec (floatWidth e m))) :
    Ends (convertFloat (μ := SetM) e m e' m' a) := by
  cases a <;> first | exact pure_ends _ | (dsimp only [convertFloat]; exact floatResult_ends e' m' _)

/-- A morphism that keeps choice and UB maps the rule of `fpext` and
`fptrunc` in one monad to their rule in the other. -/
theorem convertFloat_map {μ ν : Type → Type} [Monad μ] [Monad ν] [MonadChoice μ] [MonadChoice ν]
    [MonadUB μ] [MonadUB ν] (φ : MonadMorphism μ ν) (hk : φ.KeepsChoiceUB) (e m e' m' : Nat)
    (a : PoisonOr (BitVec (floatWidth e m))) :
    φ.map (convertFloat (μ := μ) e m e' m' a) = convertFloat e m e' m' a := by
  cases a <;> first | exact φ.map_pure _ | (dsimp only [convertFloat]; exact floatResult_map φ hk _)

section
variable (e m e' m' : Nat)

/-- The op instance of `fpext`, with `ext`, or of `fptrunc`, from
`float<e,m>` to `float<e',m'>`. -/
def convertOp : Bool → Op
  | true => .fpext e m e' m'
  | false => .fptrunc e m e' m'

/-- `fpext` and `fptrunc` propagate poison: a poison operand gives only a
poison result, and they are never UB. -/
theorem convertFloat_propagatesPoison (ext : Bool) :
    PropagatesPoison (d := CoreDialect) (convertOp e m e' m' ext) := by
  cases ext <;> exact {
    poisonOut := fun
      | .cons a .nil, h, _, hrs => by
        have hp : a = .poison := h.elim id False.elim
        subst hp
        obtain ⟨v, hv, h⟩ := oneFloat_ok (convertFloat_ends e m e' m' _) hrs
        cases hv
        cases h
        exact ⟨rfl, trivial⟩
    ubByOwnRules := fun
      | .cons a .nil, r, _, hub => absurd hub (oneFloat_not_ub (convertFloat_ends e m e' m' a) r) }

/-- `fpext` and `fptrunc` return a result on a defined operand. -/
theorem convertFloat_returnsOnDefined (ext : Bool) :
    ReturnsOnDefined (d := CoreDialect) (convertOp e m e' m' ext) := by
  obtain ⟨v, hv⟩ := (convertFloat_ends e m e' m' (.value 0)).some
  cases ext <;>
  · refine ⟨.cons (.value 0) .nil, ?_, _, oneFloat_of hv⟩
    rintro (h | h) <;> cases h

/-- `fpext` and `fptrunc` have an outcome on every operand. -/
theorem convertFloat_total (ext : Bool) :
    OpTotal (d := CoreDialect) (convertOp e m e' m' ext) := by
  cases ext <;> exact fun
    | .cons a .nil =>
      ⟨fun _ => by
        obtain ⟨_, hv⟩ := (convertFloat_ends e m e' m' a).some
        exact ⟨_, oneFloat_of hv⟩, fun h => nomatch h⟩

/-- `fpext` and `fptrunc` are monotone. -/
theorem convertFloat_monotone (ext : Bool) :
    OpMonotone (d := CoreDialect) (convertOp e m e' m' ext) := by
  cases ext <;>
  · intro args args' h
    refine ⟨fun _ => ?_, fun h => nomatch h⟩
    match args, args', h with
    | .cons a .nil, .cons a' .nil, ⟨ha, _⟩ =>
      cases a with
      | poison => exact oneFloat_poison_isRefinedBy (convertFloat_ends e m e' m' a')
      | value x =>
        cases a' with
        | poison => exact ha.elim
        | value x' =>
          have hx : x = x' := ha
          subst hx
          exact SetM.isRefinedBy_refl (HVector.forall₂_refl Core.Ty.isRefinedBy_refl) _

/-- `fpext` and `fptrunc` are never UB. -/
theorem convertFloat_neverUB (ext : Bool) :
    NeverUBSetM (d := CoreDialect) (convertOp e m e' m' ext) := by
  cases ext <;> exact fun
    | .cons a .nil, r =>
      ⟨fun _ => oneFloat_not_ub (convertFloat_ends e m e' m' a) r, fun h => nomatch h⟩

/-- On a defined operand, `fpext` and `fptrunc` give a defined result. -/
theorem convertFloat_makesNoPoison (ext : Bool) :
    MakesNoPoisonSetM (d := CoreDialect) (convertOp e m e' m' ext) := by
  cases ext <;> exact fun _ args hd rs hr => match args, hd, hr with
    | .cons a .nil, hd, hr => by
      cases a with
      | poison => exact absurd (.inl rfl) hd
      | value x =>
        obtain ⟨v, hv, ⟨⟩⟩ := oneFloat_ok (convertFloat_ends e m e' m' _) hr
        obtain ⟨_, h⟩ :=
          floatResult_defined e' m' _ _ (by dsimp only [convertFloat] at hv; exact hv)
        cases h
        exact oneFloat_defined

end

end Fir.Core
