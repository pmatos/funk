import Fir.Core.FloatArithLaws
import Fir.Core.FloatCompareLaws

/-!
# Dropping fast-math flags refines

A fast-math flag only adds ways for a float op to end: `nnan` and `ninf`
add poison, which every value refines, and `nsz` adds the zero of the
other sign. So the op with fewer flags refines the op with more, on the
same operands (ADR-2026-11-09-1549): every way the op with fewer flags may
end is allowed by a way the op with more flags may end. This holds for
`fadd`, `fsub`, `fmul`, `fdiv`, `fneg`, `fabs`, `sqrt`, `fma` and `fcmp`,
at every format, for any set of flags dropped.

Two uses follow. A pass may drop a flag. And native code, which ignores
the flags, refines the flagged op whenever it refines the op without
flags, since no flags are among every flags: `FastMath.le_none`.
-/

namespace Fir.Core

/-- No flags are among every flags. -/
theorem FastMath.le_none (fl : FastMath) : FastMath.Le {} fl :=
  ⟨nofun, nofun, nofun⟩

section
variable {e m : Nat}

/-- A rule that gives one float, whose every value under fewer flags is
a value under more or poison under more, is refined by the rule under
more flags. -/
theorem oneFloat_drop {s t : SetM (PoisonOr (BitVec (floatWidth e m)))} (ht : Ends t)
    (h : ∀ v, t (.ok v) → s (.ok .poison) ∨ s (.ok v)) :
    SetM.IsRefinedBy (HVector.Forall₂ TyRefinement.IsRefinedBy) (oneFloat s) (oneFloat t) :=
  fun ev hev => by
    obtain ⟨v, hv, rfl⟩ := oneFloat_ok ht hev
    rcases h v hv with hp | hs
    · exact ⟨_, oneFloat_of hp, trivial, trivial⟩
    · exact ⟨_, oneFloat_of hs, HVector.forall₂_refl Core.Ty.isRefinedBy_refl _⟩

variable {fl fl' : FastMath}

/-- The rules of `fadd`, `fsub`, `fmul` and `fdiv` under fewer flags give
values that the rules under more give, or the latter give poison. -/
theorem fbinValues_drop (hle : fl'.Le fl) (o : FBin) (a b : PoisonOr (BitVec (floatWidth e m)))
    {v : PoisonOr (BitVec (floatWidth e m))} (h : fbinValues (μ := SetM) o fl' a b (.ok v)) :
    fbinValues (μ := SetM) o fl a b (.ok .poison) ∨ fbinValues (μ := SetM) o fl a b (.ok v) := by
  cases a <;> cases b <;> first | exact .inr h |
    (dsimp only [fbinValues] at h ⊢; exact floatResult_drop hle h)

/-- The rules of `fneg`, `fabs` and `sqrt` under fewer flags give values
that the rules under more give, or the latter give poison. -/
theorem funaryValue_drop (hle : fl'.Le fl) (o : FUnary) (a : PoisonOr (BitVec (floatWidth e m)))
    {v : PoisonOr (BitVec (floatWidth e m))} (h : funaryValue (μ := SetM) o fl' a (.ok v)) :
    funaryValue (μ := SetM) o fl a (.ok .poison) ∨ funaryValue (μ := SetM) o fl a (.ok v) := by
  cases a <;> first | exact .inr h | (dsimp only [funaryValue] at h ⊢; exact floatResult_drop hle h)

/-- The rule of `fma` under fewer flags gives values that the rule under
more gives, or the latter gives poison. -/
theorem fmaValues_drop (hle : fl'.Le fl) (a b c : PoisonOr (BitVec (floatWidth e m)))
    {v : PoisonOr (BitVec (floatWidth e m))} (h : fmaValues (μ := SetM) fl' a b c (.ok v)) :
    fmaValues (μ := SetM) fl a b c (.ok .poison) ∨ fmaValues (μ := SetM) fl a b c (.ok v) := by
  cases a <;> cases b <;> cases c <;> first | exact .inr h |
    (dsimp only [fmaValues] at h ⊢; exact floatResult_drop hle h)

/-- `fcmp` under more flags gives poison, or what it gives under fewer. -/
theorem fcmpValues_drop (hle : fl'.Le fl) (p : FPred) (a b : PoisonOr (BitVec (floatWidth e m))) :
    fcmpValues p fl a b ⊑ fcmpValues p fl' a b := by
  cases a with
  | poison => trivial
  | value x =>
    cases b with
    | poison => trivial
    | value y =>
      simp only [fcmpValues]
      by_cases hb : operandsBreak fl e m [x, y] = true
      · simp only [hb, ↓reduceIte]
        trivial
      · have hb' : ¬ operandsBreak fl' e m [x, y] = true := fun h' => hb (operandsBreak_mono hle h')
        simp only [hb, hb', Bool.false_eq_true, ↓reduceIte]
        exact PoisonOr.isRefinedBy_refl _

end

/-! # The ops -/

section
variable {fl fl' : FastMath} (hle : fl'.Le fl) (e m : Nat)
include hle

/-- `fadd`, `fsub`, `fmul` and `fdiv` with fewer flags refine the op with
more, on every operands. -/
theorem fbin_drop (o : FBin) (args : HVector toType (Fir.sig (d := CoreDialect) (.fbin o fl e m))) :
    SetM.IsRefinedBy (HVector.Forall₂ TyRefinement.IsRefinedBy)
      (DialectDenote.denote (d := CoreDialect) (.fbin o fl e m) args)
      (DialectDenote.denote (d := CoreDialect) (.fbin o fl' e m) args) :=
  match args with
  | .cons a (.cons b .nil) => oneFloat_drop (fbinValues_ends o fl' a b) fun _ h => fbinValues_drop hle o a b h

/-- `fneg`, `fabs` and `sqrt` with fewer flags refine the op with more, on
every operand. -/
theorem funary_drop (o : FUnary)
    (args : HVector toType (Fir.sig (d := CoreDialect) (.funary o fl e m))) :
    SetM.IsRefinedBy (HVector.Forall₂ TyRefinement.IsRefinedBy)
      (DialectDenote.denote (d := CoreDialect) (.funary o fl e m) args)
      (DialectDenote.denote (d := CoreDialect) (.funary o fl' e m) args) :=
  match args with
  | .cons a .nil => oneFloat_drop (funaryValue_ends o fl' a) fun _ h => funaryValue_drop hle o a h

/-- `fma` with fewer flags refines `fma` with more, on every operands. -/
theorem fma_drop (args : HVector toType (Fir.sig (d := CoreDialect) (.fma fl e m))) :
    SetM.IsRefinedBy (HVector.Forall₂ TyRefinement.IsRefinedBy)
      (DialectDenote.denote (d := CoreDialect) (.fma fl e m) args)
      (DialectDenote.denote (d := CoreDialect) (.fma fl' e m) args) :=
  match args with
  | .cons a (.cons b (.cons c .nil)) =>
    oneFloat_drop (fmaValues_ends fl' a b c) fun _ h => fmaValues_drop hle a b c h

/-- `fcmp` with fewer flags refines `fcmp` with more, on every operands,
with every predicate. -/
theorem fcmp_drop (p : FPred) (args : HVector toType (Fir.sig (d := CoreDialect) (.fcmp p fl e m))) :
    SetM.IsRefinedBy (HVector.Forall₂ TyRefinement.IsRefinedBy)
      (DialectDenote.denote (d := CoreDialect) (.fcmp p fl e m) args)
      (DialectDenote.denote (d := CoreDialect) (.fcmp p fl' e m) args) :=
  match args with
  | .cons a (.cons b .nil) => fun ev hev => by
    cases hev
    exact ⟨_, rfl, fcmpValues_drop hle p a b, trivial⟩

end

end Fir.Core
