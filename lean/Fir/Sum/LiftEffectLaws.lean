import Fir.Sum.LiftPoisonLaws
import Fir.Sum.EffectLaws

/-!
# The lift of an extension lawful in its effects is lawful in its effects

The lift of an extension that meets the effect obligations over `dep` meets
them over `big` (`Dialect.lift.lawfulEffects`), when the inclusion is lawful
and `e` accepts each type of `dep` whose inclusion `big` accepts: the
conditions under which the lift is lawful for poison. Each op of the lift
has `e`'s effects and runs by `e`'s rule on the same values, which only
cross the inclusion. An op ends in UB in the lift exactly when it does in
`e`, and a lawful inclusion keeps which values are poison. The sum
`big ⊞ e.lift dep ι` is then lawful in its effects by the theorem on sums
(`Dialect.lift.sum_lawfulEffects`).
-/

namespace Fir

section
variable {A B : Type} [TyDenote A] [TyDenote B] {ι : TyIncl A B} [TyPoison A] [TyPoison B]
  [TyRefinement A] [TyRefinement B]

/-- A vector crossed up holds poison exactly when it did. -/
theorem HVector.any_up (h : ι.Lawful) : ∀ {ts : List A} (xs : HVector toType ts),
    (HVector.up ι xs).Any TyPoison.IsPoison ↔ xs.Any TyPoison.IsPoison
  | [], .nil => Iff.rfl
  | _ :: _, .cons x xs => or_congr (h.isPoison_up x) (HVector.any_up h xs)

end

namespace Dialect.lift

variable {e dep big : Dialect} [TyDenote dep.Ty] [TyDenote big.Ty] [TyDenote e.Ty]
  {ι : TyIncl dep.Ty big.Ty} [DialectSignature (dep.over e)] [DialectDenote (dep.over e) SetM]

/-- An op of `e` that never ends in UB over `dep` never does in the lift. -/
theorem neverUB_lift {o : e.Op} (h : NeverUB (d := dep.over e) o) :
    NeverUB (d := big.over (e.lift dep ι)) o := fun args r =>
  ⟨fun ht hden => by
    rcases (HVector.map_up _ _).1 hden with ⟨a, -, he⟩ | ⟨r', hr, he⟩
    · cases he
    · cases he
      exact (h (HVector.down (incl e ι) args) r).1 ht hr,
  fun ht hex => (h (HVector.down (incl e ι) args) r).2 ht hex⟩

variable [TyPoison dep.Ty] [TyPoison big.Ty] [TyPoison e.Ty]
  [TyRefinement dep.Ty] [TyRefinement big.Ty] [TyRefinement e.Ty]

/-- An op of `e` that makes no poison over `dep` makes none in the lift,
when the inclusion is lawful. -/
theorem makesNoPoison_lift (hι : ι.Lawful) {o : e.Op} (h : MakesNoPoison (d := dep.over e) o) :
    MakesNoPoison (d := big.over (e.lift dep ι)) o := fun ht args hnp rs hden => by
  rcases (HVector.map_up _ _).1 hden with ⟨a, ha, he⟩ | ⟨r, -, he⟩
  · cases he
    exact fun hp =>
      h ht _ (fun hd => hnp ((HVector.any_down (incl_lawful e hι) args).1 hd)) a ha
        ((HVector.any_up (incl_lawful e hι) a).1 hp)
  · cases he

variable [DialectEffects (dep.over e)] [DialectCall (dep.over e)]
  [DialectValidation big] [DialectValidation (dep.over e)]

/-- The lift of an extension lawful in its effects is lawful in its effects,
when the inclusion is lawful and `e` accepts each type of `dep` whose
inclusion `big` accepts. -/
theorem lawfulEffects [h : LawfulDialectEffects (dep.over e)] (hι : ι.Lawful)
    (hty : ∀ t : dep.Ty, validTy (ι.incl t) → validTy (d := dep.over e) (.inl t)) :
    LawfulDialectEffects (big.over (e.lift dep ι)) where
  neverUB o hv hc hu := neverUB_lift (h.neverUB o (typesValid_lift hty hv) hc hu)
  makesNoPoison o hv hc hp :=
    makesNoPoison_lift hι (h.makesNoPoison o (typesValid_lift hty hv) hc hp)
  notControl o hc := h.notControl o hc

variable [DialectSignature big] [DialectDenote big SetM] [DialectEffects big] [DialectCall big]

/-- The sum of a `big` lawful in its effects and the lift of an extension
lawful in its effects is lawful in its effects, when the inclusion is
lawful and `e` accepts each type of `dep` whose inclusion `big` accepts. -/
theorem sum_lawfulEffects [LawfulDialectEffects big] [LawfulDialectEffects (dep.over e)]
    (hι : ι.Lawful)
    (hty : ∀ t : dep.Ty, validTy (ι.incl t) → validTy (d := dep.over e) (.inl t)) :
    LawfulDialectEffects (big ⊞ e.lift dep ι) :=
  have := lawfulEffects (e := e) (big := big) hι hty
  Dialect.sum.lawfulEffects fun _ h => h

end Dialect.lift

end Fir
