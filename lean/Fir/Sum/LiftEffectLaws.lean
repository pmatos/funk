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
`big ⊞ e.lift dep ι μ` is then lawful in its effects by the theorem on sums
(`Dialect.lift.sum_lawfulEffects`).

The lift's semantics with memory runs an op of `e` by `e`'s at the run's
naming composed with the lift's memory map, so the op meets the memory
obligations in the lift because it meets them in `e` at that naming.
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

open Memory

section

/-! # Memory -/

variable {e dep big : Dialect} [TyDenote dep.Ty] [TyDenote big.Ty] [TyDenote e.Ty]
  {ι : TyIncl dep.Ty big.Ty} [DialectSignature (dep.over e)]
  [DialectEffects dep] [DialectEffects big] [DialectEffects (dep.over e)] [DialectMemOver dep e]
  {μ : DialectEffects.Mem dep → DialectEffects.Mem big}

/-- The lift's semantics with memory, wherever a run names its memories by
`ρ`: an op of the lift runs by `e`'s rule, where the run names each memory
of `e` as `ρ` names its image under the lift's memory map. -/
instance instDialectMemDenote [DialectMemDenote (dep.over e)] :
    DialectMemDenote (big.over (e.lift dep ι μ)) where
  denoteAt unit ρ :=
    letI := DialectMemDenote.denoteAt (d := dep.over e) unit (ρ ∘ liftMem μ)
    instDialectDenote

variable [DialectMemDenote (dep.over e)] {N : Type} [DecidableEq N] (unit : N → Nat)
  (ρ : DialectEffects.Mem (big.over (e.lift dep ι μ)) → N)
  {P : {α : Type} → StateT (Memories N unit) SetM α → Prop}

/-- A property that mapping the results keeps holds of what an op of the
lift runs by its own rule, when it holds of the op in `e`, where the run
names `e`'s memories through the lift's memory map. -/
theorem ownRuleHas_lift (hP : ∀ {α β : Type} (f : α → β) (c : StateT (Memories N unit) SetM α),
      P c → P (f <$> c)) {o : e.Op}
    (h : OwnRuleHas (d := dep.over e) unit (ρ ∘ liftMem μ) P o) :
    OwnRuleHas (d := big.over (e.lift dep ι μ)) unit ρ P o := fun args =>
  ⟨fun ht => hP _ _ ((h (HVector.down (incl e ι μ) args)).1 ht),
    fun ht => (h (HVector.down (incl e ι μ) args)).2 ht⟩

omit [DecidableEq N] in
/-- An op of `e` that never ends in UB over `dep` never does in the lift. -/
theorem neverUB_lift {o : e.Op} (h : NeverUB (d := dep.over e) o) :
    NeverUB (d := big.over (e.lift dep ι μ)) o :=
  fun unit ρ => ownRuleHas_lift unit ρ (fun f _ h => NoUB.map f h) (h unit (ρ ∘ liftMem μ))

/-- An op of `e` that makes no poison over `dep` makes none in the lift,
when the inclusion is lawful. -/
theorem makesNoPoison_lift [TyPoison dep.Ty] [TyPoison big.Ty] [TyPoison e.Ty]
    [TyRefinement dep.Ty] [TyRefinement big.Ty] [TyRefinement e.Ty] (hι : ι.Lawful) {o : e.Op}
    (h : MakesNoPoison (d := dep.over e) o) :
    MakesNoPoison (d := big.over (e.lift dep ι μ)) o := by
  intro ht N _ unit ρ args hnp S rs S' hden
  rcases (SetM.stateMap_apply _ _ S _).1 hden with ⟨a, S'', ha, he⟩ | ⟨_, -, he⟩
  · cases he
    exact fun hp => h ht unit (ρ ∘ liftMem μ) _
      (fun hd => hnp ((HVector.any_down (incl_lawful e μ hι) args).1 hd)) S a _ ha
      ((HVector.any_up (incl_lawful e μ hι) a).1 hp)
  · cases he

/-- The lift of an extension that lifts the set monad over `dep` lifts it:
each op runs by `e`'s rule in the set monad, with its values crossing the
inclusion, and keeps the memories. -/
instance liftsSetM [DialectDenote (dep.over e) SetM] [LiftsSetM (dep.over e)] :
    LiftsSetM (big.over (e.lift dep ι μ)) where
  lifts unit ρ := by
    dsimp only [DialectMemDenote.denoteAt]
    rw [LiftsSetM.lifts (d := dep.over e)]
    exact DialectDenote.ext (fun _ _ => ((MonadMorphism.liftState SetM _).map_map _ _).symm)
      (fun _ _ => rfl)

end

variable {e dep big : Dialect} [TyDenote dep.Ty] [TyDenote big.Ty] [TyDenote e.Ty]
  {ι : TyIncl dep.Ty big.Ty} [DialectSignature (dep.over e)]
  [TyPoison dep.Ty] [TyPoison big.Ty] [TyPoison e.Ty]
  [TyRefinement dep.Ty] [TyRefinement big.Ty] [TyRefinement e.Ty]

variable [DialectEffects dep] [DialectEffects big] [DialectEffects (dep.over e)]
  [DialectMemOver dep e] [DialectMemDenote (dep.over e)] [DialectCall (dep.over e)]
  [DialectValidation big] [DialectValidation (dep.over e)]

/-- The lift of an extension lawful in its effects is lawful in its effects,
when the inclusion is lawful and `e` accepts each type of `dep` whose
inclusion `big` accepts. An op of the lift meets the memory obligations
where the run names `e`'s memories through the lift's memory map. -/
theorem lawfulEffects {μ : DialectEffects.Mem dep → DialectEffects.Mem big}
    [h : LawfulDialectEffects (dep.over e)] (hι : ι.Lawful)
    (hty : ∀ t : dep.Ty, validTy (ι.incl t) → validTy (d := dep.over e) (.inl t)) :
    LawfulDialectEffects (big.over (e.lift dep ι μ)) where
  neverUB o hv hc hu := neverUB_lift (h.neverUB o (typesValid_lift hty hv) hc hu)
  makesNoPoison o hv hc hp :=
    makesNoPoison_lift hι (h.makesNoPoison o (typesValid_lift hty hv) hc hp)
  notControl o hc := h.notControl o hc
  writesNot o hv hc _ _ unit ρ x hw :=
    ownRuleHas_lift unit ρ (fun f _ h => WritesNot.map f h) (h.writesNot o
      (typesValid_lift hty hv) hc unit _ x (by rw [← MemSet.map_map]; exact hw))
  readsNot o hv hc _ _ unit ρ x hr :=
    ownRuleHas_lift unit ρ (fun f _ h => ReadsNot.map f h) (h.readsNot o
      (typesValid_lift hty hv) hc unit _ x (by rw [← MemSet.map_map]; exact hr))
  allocatesNot o hv hc _ _ unit ρ x ha :=
    ownRuleHas_lift unit ρ (fun f _ h => AllocatesNot.map f h) (h.allocatesNot o
      (typesValid_lift hty hv) hc unit _ x (by rw [← MemSet.map_map]; exact ha))

variable [DialectSignature big] [DialectCall big] [DialectMemDenote big]

/-- The sum of a `big` lawful in its effects and the lift of an extension
lawful in its effects is lawful in its effects, when the inclusion is
lawful and `e` accepts each type of `dep` whose inclusion `big` accepts. -/
theorem sum_lawfulEffects {μ : DialectEffects.Mem dep → DialectEffects.Mem big}
    [LawfulDialectEffects big] [LawfulDialectEffects (dep.over e)] (hι : ι.Lawful)
    (hty : ∀ t : dep.Ty, validTy (ι.incl t) → validTy (d := dep.over e) (.inl t)) :
    LawfulDialectEffects (big ⊞ e.lift dep ι μ) :=
  have := lawfulEffects (e := e) (big := big) (μ := μ) hι hty
  Dialect.sum.lawfulEffects fun _ h => h

end Dialect.lift

end Fir
