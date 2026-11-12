import Fir.Core.FloatResultLaws
import Fir.Core.Poison
import Fir.Execution.EffectLaws

/-!
# Float arithmetic is lawful

`fadd`, `fsub`, `fmul`, `fdiv`, `fneg`, `fabs`, `sqrt` and `fma`, at every
format and with every fast-math flag, meet the obligations of the poison
classes section. Each propagates poison (ADR-2026-10-29-2006), so it meets
both poison clauses, returns a result on some operands with no poison, and
is total and monotone. Each also meets the effect obligations of its
declaration: it is never UB, and without `nnan` and `ninf` it gives a
defined result on operands with no poison (ADR-2026-11-09-1549).

On defined operands each rule gives a float result (the section on what a
float result may be): it has a way to end, each way is a value, and it is
poison only when `nnan` or `ninf` is set. A poison operand gives exactly a
poison result, which every result refines, and defined operands are
refined only by themselves, so each rule is monotone. None of this looks
at what the model computes: the proofs hold for any operation of the
model, and for every NaN and sign that a choice gives.

Each rule, run in `fir-ref`'s tree of choices, has the set monad's rule as
its set, as `freeze`'s does: the last section proves it, for the modes of
`fir-ref run`.
-/

namespace Fir.Core

open Float.Model

/-- The rules of `fadd`, `fsub`, `fmul` and `fdiv` have a way to end, and
are never UB. -/
theorem fbinValues_ends (o : FBin) (fl : FastMath) (a b : PoisonOr (BitVec (floatWidth e m))) :
    Ends (fbinValues (μ := SetM) o fl a b) := by
  cases a <;> cases b <;> first | exact pure_ends _ | (dsimp only [fbinValues]; exact floatResult_ends fl e m _ _)

/-- The rules of `fneg`, `fabs` and `sqrt` have a way to end, and are
never UB. -/
theorem funaryValue_ends (o : FUnary) (fl : FastMath) (a : PoisonOr (BitVec (floatWidth e m))) :
    Ends (funaryValue (μ := SetM) o fl a) := by
  cases a <;> first | exact pure_ends _ | (dsimp only [funaryValue]; exact floatResult_ends fl e m _ _)

/-- The rule of `fma` has a way to end, and is never UB. -/
theorem fmaValues_ends (fl : FastMath) (a b c : PoisonOr (BitVec (floatWidth e m))) :
    Ends (fmaValues (μ := SetM) fl a b c) := by
  cases a <;> cases b <;> cases c <;>
    first | exact pure_ends _ | (dsimp only [fmaValues]; exact floatResult_ends fl e m _ _)

/-! # Rules that give one float -/

section
variable {e m : Nat} {s : SetM (PoisonOr (BitVec (floatWidth e m)))}

/-- A rule that gives the one value of `s`. -/
abbrev oneFloat (s : SetM (PoisonOr (BitVec (floatWidth e m)))) :
    SetM (HVector toType [Ty.float e m]) := do
  let v ← s
  pure (.cons v .nil)

/-- A rule that gives one value of `s`, when `s` ends and is never UB,
ends with one of the values of `s`. -/
theorem oneFloat_ok (hs : Ends s) {ev : Ev (HVector toType [Ty.float e m])}
    (h : oneFloat s ev) : ∃ v, s (.ok v) ∧ ev = .ok (.cons v .nil) := by
  rcases h with ⟨v, hv, h⟩ | ⟨r, hr, _⟩
  · exact ⟨v, hv, h⟩
  · obtain ⟨_, h⟩ := hs.ok _ hr
    cases h

/-- A rule that gives one value of `s` ends with each of them. -/
theorem oneFloat_of {v : PoisonOr (BitVec (floatWidth e m))} (hv : s (.ok v)) :
    oneFloat s (.ok (.cons v .nil)) :=
  .inl ⟨v, hv, rfl⟩

/-- A rule that gives one value of `s`, when `s` ends and is never UB, is
never UB. -/
theorem oneFloat_not_ub (hs : Ends s) (r : String) : ¬ oneFloat s (.ub r) := fun h => by
  obtain ⟨_, _, h⟩ := oneFloat_ok hs h
  cases h

/-- The rule refines itself on poison: when `s` gives only poison, every
way that `t` ends with one value is refined by `s`'s. -/
theorem oneFloat_poison_isRefinedBy {t : SetM (PoisonOr (BitVec (floatWidth e m)))}
    (ht : Ends t) :
    SetM.IsRefinedBy (HVector.Forall₂ TyRefinement.IsRefinedBy)
      (oneFloat (pure .poison)) (oneFloat t) := fun ev hev => by
  obtain ⟨_, _, rfl⟩ := oneFloat_ok ht hev
  exact ⟨_, oneFloat_of rfl, trivial, trivial⟩

/-- A vector of one defined float holds no poison. -/
theorem oneFloat_defined {b : BitVec (floatWidth e m)} :
    ¬ (HVector.cons (f := toType) (as := []) (a := Ty.float e m)
      (PoisonOr.value b : PoisonOr (BitVec (floatWidth e m))) .nil).Any
      TyPoison.IsPoison
  | .inl h => nomatch h

end

/-! # The float ops of two operands -/

section
variable (o : FBin) (fl : FastMath) (e m : Nat)

/-- `fadd`, `fsub`, `fmul` and `fdiv` propagate poison: a poison operand
gives only a poison result, and they are never UB. -/
theorem fbin_propagatesPoison : PropagatesPoison (d := CoreDialect) (.fbin o fl e m) where
  poisonOut
    | .cons a (.cons b .nil), h, _, hrs => by
      have hp : a = .poison ∨ b = .poison := h.imp_right fun h => h.elim id False.elim
      have hs : fbinValues (μ := SetM) o fl a b = pure .poison := by
        rcases hp with rfl | rfl
        · rfl
        · cases a <;> rfl
      obtain ⟨v, hv, h⟩ := oneFloat_ok (fbinValues_ends o fl a b) hrs
      rw [hs] at hv
      cases hv
      cases h
      exact ⟨rfl, trivial⟩
  ubByOwnRules
    | .cons a (.cons b .nil), r, _, hub => absurd hub (oneFloat_not_ub (fbinValues_ends o fl a b) r)

/-- `fadd`, `fsub`, `fmul` and `fdiv` return a result on two defined
operands. -/
theorem fbin_returnsOnDefined : ReturnsOnDefined (d := CoreDialect) (.fbin o fl e m) := by
  obtain ⟨v, hv⟩ := (fbinValues_ends (e := e) (m := m) o fl (.value 0) (.value 0)).some
  refine ⟨.cons (.value 0) (.cons (.value 0) .nil), ?_, _, oneFloat_of hv⟩
  rintro (h | h | h) <;> cases h

/-- `fadd`, `fsub`, `fmul` and `fdiv` have an outcome on every operand
vector. -/
theorem fbin_total : OpTotal (d := CoreDialect) (.fbin o fl e m) := fun
  | .cons a (.cons b .nil) =>
    ⟨fun _ => by
      obtain ⟨_, hv⟩ := (fbinValues_ends o fl a b).some
      exact ⟨_, oneFloat_of hv⟩, fun h => nomatch h⟩

/-- `fadd`, `fsub`, `fmul` and `fdiv` are monotone. -/
theorem fbin_monotone : OpMonotone (d := CoreDialect) (.fbin o fl e m) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a (.cons b .nil), .cons a' (.cons b' .nil), ⟨ha, hb, _⟩ =>
    cases a with
    | poison => exact oneFloat_poison_isRefinedBy (fbinValues_ends o fl a' b')
    | value x =>
      cases b with
      | poison => exact oneFloat_poison_isRefinedBy (fbinValues_ends o fl a' b')
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
            exact SetM.isRefinedBy_refl (HVector.forall₂_refl Core.Ty.isRefinedBy_refl) _

/-- `fadd`, `fsub`, `fmul` and `fdiv` are never UB. -/
theorem fbin_neverUB : NeverUBSetM (d := CoreDialect) (.fbin o fl e m) := fun
  | .cons a (.cons b .nil), r => ⟨fun _ => oneFloat_not_ub (fbinValues_ends o fl a b) r, fun h => nomatch h⟩

/-- On defined operands, `fadd`, `fsub`, `fmul` and `fdiv` give a defined
result when no flag may make poison. -/
theorem fbin_makesNoPoison (hm : fl.mayPoison = false) :
    MakesNoPoisonSetM (d := CoreDialect) (.fbin o fl e m) := fun _ args hd rs hr =>
  match args, hd, hr with
  | .cons a (.cons b .nil), hd, hr => by
    cases a with
    | poison => exact absurd (.inl rfl) hd
    | value x =>
      cases b with
      | poison => exact absurd (.inr (.inl rfl)) hd
      | value y =>
        obtain ⟨v, hv, ⟨⟩⟩ := oneFloat_ok (fbinValues_ends o fl _ _) hr
        obtain ⟨_, h, hd⟩ := floatResult_ok (by dsimp only [fbinValues] at hv; exact hv)
        cases h
        obtain ⟨_, rfl⟩ := hd hm
        exact oneFloat_defined

end

/-! # The float ops of one operand -/

section
variable (o : FUnary) (fl : FastMath) (e m : Nat)

/-- `fneg`, `fabs` and `sqrt` propagate poison: a poison operand gives
only a poison result, and they are never UB. -/
theorem funary_propagatesPoison : PropagatesPoison (d := CoreDialect) (.funary o fl e m) where
  poisonOut
    | .cons a .nil, h, _, hrs => by
      have hp : a = .poison := h.elim id False.elim
      subst hp
      obtain ⟨v, hv, h⟩ := oneFloat_ok (funaryValue_ends o fl _) hrs
      cases hv
      cases h
      exact ⟨rfl, trivial⟩
  ubByOwnRules
    | .cons a .nil, r, _, hub => absurd hub (oneFloat_not_ub (funaryValue_ends o fl a) r)

/-- `fneg`, `fabs` and `sqrt` return a result on a defined operand. -/
theorem funary_returnsOnDefined : ReturnsOnDefined (d := CoreDialect) (.funary o fl e m) := by
  obtain ⟨v, hv⟩ := (funaryValue_ends (e := e) (m := m) o fl (.value 0)).some
  refine ⟨.cons (.value 0) .nil, ?_, _, oneFloat_of hv⟩
  rintro (h | h) <;> cases h

/-- `fneg`, `fabs` and `sqrt` have an outcome on every operand. -/
theorem funary_total : OpTotal (d := CoreDialect) (.funary o fl e m) := fun
  | .cons a .nil =>
    ⟨fun _ => by
      obtain ⟨_, hv⟩ := (funaryValue_ends o fl a).some
      exact ⟨_, oneFloat_of hv⟩, fun h => nomatch h⟩

/-- `fneg`, `fabs` and `sqrt` are monotone. -/
theorem funary_monotone : OpMonotone (d := CoreDialect) (.funary o fl e m) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a .nil, .cons a' .nil, ⟨ha, _⟩ =>
    cases a with
    | poison => exact oneFloat_poison_isRefinedBy (funaryValue_ends o fl a')
    | value x =>
      cases a' with
      | poison => exact ha.elim
      | value x' =>
        have hx : x = x' := ha
        subst hx
        exact SetM.isRefinedBy_refl (HVector.forall₂_refl Core.Ty.isRefinedBy_refl) _

/-- `fneg`, `fabs` and `sqrt` are never UB. -/
theorem funary_neverUB : NeverUBSetM (d := CoreDialect) (.funary o fl e m) := fun
  | .cons a .nil, r => ⟨fun _ => oneFloat_not_ub (funaryValue_ends o fl a) r, fun h => nomatch h⟩

/-- On a defined operand, `fneg`, `fabs` and `sqrt` give a defined
result when no flag may make poison. -/
theorem funary_makesNoPoison (hm : fl.mayPoison = false) :
    MakesNoPoisonSetM (d := CoreDialect) (.funary o fl e m) :=
  fun _ args hd rs hr => match args, hd, hr with
  | .cons a .nil, hd, hr => by
    cases a with
    | poison => exact absurd (.inl rfl) hd
    | value x =>
      obtain ⟨v, hv, ⟨⟩⟩ := oneFloat_ok (funaryValue_ends o fl _) hr
      obtain ⟨_, h, hd⟩ := floatResult_ok (by dsimp only [funaryValue] at hv; exact hv)
      cases h
      obtain ⟨_, rfl⟩ := hd hm
      exact oneFloat_defined

end

/-! # Fused multiply-add -/

section
variable (fl : FastMath) (e m : Nat)

/-- `fma` propagates poison: a poison operand gives only a poison result,
and it is never UB. -/
theorem fma_propagatesPoison : PropagatesPoison (d := CoreDialect) (.fma fl e m) where
  poisonOut
    | .cons a (.cons b (.cons c .nil)), h, _, hrs => by
      have hs : fmaValues (μ := SetM) fl a b c = pure .poison := by
        rcases h with h | h | h | h
        · cases (show a = .poison from h); rfl
        · cases (show b = .poison from h); cases a <;> rfl
        · cases (show c = .poison from h); cases a <;> cases b <;> rfl
        · exact h.elim
      obtain ⟨v, hv, h⟩ := oneFloat_ok (fmaValues_ends fl a b c) hrs
      rw [hs] at hv
      cases hv
      cases h
      exact ⟨rfl, trivial⟩
  ubByOwnRules
    | .cons a (.cons b (.cons c .nil)), r, _, hub =>
      absurd hub (oneFloat_not_ub (fmaValues_ends fl a b c) r)

/-- `fma` returns a result on three defined operands. -/
theorem fma_returnsOnDefined : ReturnsOnDefined (d := CoreDialect) (.fma fl e m) := by
  obtain ⟨v, hv⟩ := (fmaValues_ends (e := e) (m := m) fl (.value 0) (.value 0) (.value 0)).some
  refine ⟨.cons (.value 0) (.cons (.value 0) (.cons (.value 0) .nil)), ?_, _, oneFloat_of hv⟩
  rintro (h | h | h | h) <;> cases h

/-- `fma` has an outcome on every operand vector. -/
theorem fma_total : OpTotal (d := CoreDialect) (.fma fl e m) := fun
  | .cons a (.cons b (.cons c .nil)) =>
    ⟨fun _ => by
      obtain ⟨_, hv⟩ := (fmaValues_ends fl a b c).some
      exact ⟨_, oneFloat_of hv⟩, fun h => nomatch h⟩

/-- `fma` is monotone. -/
theorem fma_monotone : OpMonotone (d := CoreDialect) (.fma fl e m) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a (.cons b (.cons c .nil)), .cons a' (.cons b' (.cons c' .nil)), ⟨ha, hb, hc, _⟩ =>
    have hp := oneFloat_poison_isRefinedBy (fmaValues_ends fl a' b' c')
    cases a with
    | poison => exact hp
    | value x =>
      cases b with
      | poison => exact hp
      | value y =>
        cases c with
        | poison => exact hp
        | value z =>
          cases a' with
          | poison => exact ha.elim
          | value x' =>
            cases b' with
            | poison => exact hb.elim
            | value y' =>
              cases c' with
              | poison => exact hc.elim
              | value z' =>
                have hx : x = x' := ha
                have hy : y = y' := hb
                have hz : z = z' := hc
                subst hx hy hz
                exact SetM.isRefinedBy_refl (HVector.forall₂_refl Core.Ty.isRefinedBy_refl) _

/-- `fma` is never UB. -/
theorem fma_neverUB : NeverUBSetM (d := CoreDialect) (.fma fl e m) := fun
  | .cons a (.cons b (.cons c .nil)), r =>
    ⟨fun _ => oneFloat_not_ub (fmaValues_ends fl a b c) r, fun h => nomatch h⟩

/-- On defined operands, `fma` gives a defined result when no flag may
make poison. -/
theorem fma_makesNoPoison (hm : fl.mayPoison = false) :
    MakesNoPoisonSetM (d := CoreDialect) (.fma fl e m) :=
  fun _ args hd rs hr => match args, hd, hr with
  | .cons a (.cons b (.cons c .nil)), hd, hr => by
    cases a with
    | poison => exact absurd (.inl rfl) hd
    | value x =>
      cases b with
      | poison => exact absurd (.inr (.inl rfl)) hd
      | value y =>
        cases c with
        | poison => exact absurd (.inr (.inr (.inl rfl))) hd
        | value z =>
          obtain ⟨v, hv, ⟨⟩⟩ := oneFloat_ok (fmaValues_ends fl _ _ _) hr
          obtain ⟨_, h, hd⟩ := floatResult_ok (by dsimp only [fmaValues] at hv; exact hv)
          cases h
          obtain ⟨_, rfl⟩ := hd hm
          exact oneFloat_defined

end

/-! # The rules in the tree of choices -/

section
variable {ε : Type} {e m : Nat}

/-- The rules of `fadd`, `fsub`, `fmul` and `fdiv` in the tree of choices
have the set monad's as their set. -/
theorem fbinValues_toSet (o : FBin) (fl : FastMath) (a b : PoisonOr (BitVec (floatWidth e m))) :
    (fbinValues (μ := ChoiceTree ε) o fl a b).toSet = fbinValues o fl a b := by
  cases a <;> cases b <;> first | rfl | (dsimp only [fbinValues]; exact floatResult_toSet _ _ _ _ _)

/-- The rules of `fneg`, `fabs` and `sqrt` in the tree of choices have the
set monad's as their set. -/
theorem funaryValue_toSet (o : FUnary) (fl : FastMath) (a : PoisonOr (BitVec (floatWidth e m))) :
    (funaryValue (μ := ChoiceTree ε) o fl a).toSet = funaryValue o fl a := by
  cases a <;> first | rfl | (dsimp only [funaryValue]; exact floatResult_toSet _ _ _ _ _)

/-- The rule of `fma` in the tree of choices has the set monad's as its
set. -/
theorem fmaValues_toSet (fl : FastMath) (a b c : PoisonOr (BitVec (floatWidth e m))) :
    (fmaValues (μ := ChoiceTree ε) fl a b c).toSet = fmaValues fl a b c := by
  cases a <;> cases b <;> cases c <;>
    first | rfl | (dsimp only [fmaValues]; exact floatResult_toSet _ _ _ _ _)

end

end Fir.Core
