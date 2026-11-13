import Fir.Sum.TotalLaws
import Fir.Execution.MemoryPoison

/-!
# The sum and the lift of dialects lawful in their poison with memory

A sum is lawful in its poison with memory when its two sides are
(`Dialect.sum.lawfulMemPoison`), and so is the lift of an extension that is
(`Dialect.lift.lawfulMemPoison`), under the conditions that make them lawful
for poison in the set monad. Each op runs by its own side's rule with
memory, where the run names that side's memories through the side's memory
map, and only its operands and results change the type they are seen at,
which keeps which values are poison. Mapping the results of a computation
keeps the memories it ends with and the paths that end in UB, so an op that
propagates poison with memory in its side propagates it in the sum and in
the lift, from the same memories. Neither needs a semantics in the set
monad, so a side whose ops touch memory may take part.
-/

namespace Fir

open Memory

namespace Dialect.sum

variable {base e : Dialect} [TyDenote base.Ty] [TyDenote e.Ty] [TyPoison base.Ty] [TyPoison e.Ty]
  [DialectSignature base] [DialectSignature (base.over e)]
  [DialectEffects base] [DialectEffects (base.over e)] [DialectMemOver base e]
  [DialectMemDenote base] [DialectMemDenote (base.over e)]

/-- A base op that propagates poison with memory in the base propagates it
with memory in the sum. -/
theorem memPropagates_inl {o : base.Op} (h : MemPropagatesPoison o) :
    MemPropagatesPoison (d := base ⊞ e) (.inl o) where
  poisonOut unit ρ args hany S rs S' hden := by
    rcases (SetM.stateMap_apply _ _ S _).1 hden with ⟨a, S'', ha, he⟩ | ⟨_, -, he⟩
    · cases he
      exact (HVector.all_toSum a).2 (h.poisonOut unit (ρ ∘ DialectMemOver.ofBase) _
        ((HVector.any_ofSum args).2 hany) S a S' ha)
    · cases he
  ubByOwnRules unit ρ args S r hany hden := by
    rcases (SetM.stateMap_apply _ _ S _).1 hden with ⟨_, _, -, he⟩ | ⟨r', hr, he⟩
    · cases he
    · cases he
      obtain ⟨args', hfill, r'', hub⟩ := h.ubByOwnRules unit (ρ ∘ DialectMemOver.ofBase) _ S r
        ((HVector.any_ofSum args).2 hany) hr
      refine ⟨HVector.toSum args', ?_, r'', (SetM.stateMap_apply _ _ S _).2 (.inr ⟨r'', ?_, rfl⟩)⟩
      · rw [← isFilledBy_ofSum, HVector.ofSum_toSum]
        exact hfill
      · rw [HVector.ofSum_toSum]
        exact hub

/-- A base op that returns a result on defined operands with memory in the
base returns one in the sum. -/
theorem memReturnsOnDefined_inl {o : base.Op} (h : MemReturnsOnDefined o) :
    MemReturnsOnDefined (d := base ⊞ e) (.inl o) := by
  intro _ _ unit ρ
  obtain ⟨args, hnp, S, rs, S', hS, hrs⟩ := h unit (ρ ∘ DialectMemOver.ofBase)
  refine ⟨HVector.toSum args, ?_, S, HVector.toSum rs, S', hS,
    (SetM.stateMap_apply _ _ S _).2 (.inl ⟨rs, S', ?_, rfl⟩)⟩
  · rw [← HVector.any_ofSum, HVector.ofSum_toSum]
    exact hnp
  · rw [HVector.ofSum_toSum]
    exact hrs

variable [TyRefinement base.Ty] [TyRefinement e.Ty]
  [DialectValidation base] [DialectValidation (base.over e)]

/-- Two dialects lawful in their poison with memory make a sum lawful in its
poison with memory, when `e` accepts every type that the base accepts. -/
theorem lawfulMemPoison [h₁ : LawfulDialectMemPoison base]
    [h₂ : LawfulDialectMemPoison (base.over e)]
    (hty : ∀ t : base.Ty, validTy t → validTy (d := base.over e) (.inl t)) :
    LawfulDialectMemPoison (base ⊞ e) where
  poison_isRefinedBy {t} := match t with
    | .inl _ => fun hv p v hp => h₁.poison_isRefinedBy hv p v hp
    | .inr t => fun hv p v hp => h₂.poison_isRefinedBy (t := .inr t) hv p v hp
  propagates
    | .inl o, hv, hc => memPropagates_inl (h₁.propagates o (typesValid_inl hv) hc)
    | .inr o, hv, hc =>
      have h := h₂.propagates o (typesValid_inr hty hv) hc
      ⟨h.1, h.2⟩
  returnsOnDefined
    | .inl o, hv, hc => memReturnsOnDefined_inl (h₁.returnsOnDefined o (typesValid_inl hv) hc)
    | .inr o, hv, hc => h₂.returnsOnDefined o (typesValid_inr hty hv) hc

end Dialect.sum

namespace Dialect.lift

variable {e dep big : Dialect} [TyDenote dep.Ty] [TyDenote big.Ty] [TyDenote e.Ty]
  {ι : TyIncl dep.Ty big.Ty} [DialectSignature (dep.over e)]
  [TyPoison dep.Ty] [TyPoison big.Ty] [TyPoison e.Ty]
  [TyRefinement dep.Ty] [TyRefinement big.Ty] [TyRefinement e.Ty]
  [DialectEffects dep] [DialectEffects big] [DialectEffects (dep.over e)] [DialectMemOver dep e]
  [DialectMemDenote (dep.over e)] {μ : DialectEffects.Mem dep → DialectEffects.Mem big}

/-- An op of `e` that propagates poison with memory over `dep` propagates it
with memory in the lift, when the inclusion is lawful. -/
theorem memPropagates_lift (hι : ι.Lawful) {o : e.Op} (h : MemPropagatesPoison (d := dep.over e) o) :
    MemPropagatesPoison (d := big.over (e.lift dep ι μ)) o where
  poisonOut unit ρ args hany S rs S' hden := by
    rcases (SetM.stateMap_apply _ _ S _).1 hden with ⟨a, S'', ha, he⟩ | ⟨_, -, he⟩
    · cases he
      exact (HVector.all_up (incl_lawful e μ hι) a).2 (h.poisonOut unit (ρ ∘ liftMem μ) _
        ((HVector.any_down (incl_lawful e μ hι) args).2 hany) S a S' ha)
    · cases he
  ubByOwnRules unit ρ args S r hany hden := by
    rcases (SetM.stateMap_apply _ _ S _).1 hden with ⟨_, _, -, he⟩ | ⟨r', hr, he⟩
    · cases he
    · cases he
      obtain ⟨args', hfill, r'', hub⟩ := h.ubByOwnRules unit (ρ ∘ liftMem μ) _ S r
        ((HVector.any_down (incl_lawful e μ hι) args).2 hany) hr
      refine ⟨HVector.up (incl e ι μ) args', ?_, r'',
        (SetM.stateMap_apply _ _ S _).2 (.inr ⟨r'', ?_, rfl⟩)⟩
      · rw [← isFilledBy_down hι, HVector.down_up]
        exact hfill
      · rw [HVector.down_up]
        exact hub

/-- An op of `e` that returns a result on defined operands with memory over
`dep` returns one in the lift, when the inclusion is lawful. -/
theorem memReturnsOnDefined_lift (hι : ι.Lawful) {o : e.Op}
    (h : MemReturnsOnDefined (d := dep.over e) o) :
    MemReturnsOnDefined (d := big.over (e.lift dep ι μ)) o := by
  intro _ _ unit ρ
  obtain ⟨args, hnp, S, rs, S', hS, hrs⟩ := h unit (ρ ∘ liftMem μ)
  refine ⟨HVector.up (incl e ι μ) args, ?_, S, HVector.up (incl e ι μ) rs, S', hS,
    (SetM.stateMap_apply _ _ S _).2 (.inl ⟨rs, S', ?_, rfl⟩)⟩
  · rw [← HVector.any_down (incl_lawful e μ hι), HVector.down_up]
    exact hnp
  · rw [HVector.down_up]
    exact hrs

variable [DialectValidation big] [DialectValidation (dep.over e)]

/-- The lift of an extension lawful in its poison with memory is lawful in
its poison with memory over a `big` that is, when the inclusion is lawful
and `e` accepts each type of `dep` whose inclusion `big` accepts. -/
theorem lawfulMemPoison [DialectSignature big] [DialectMemDenote big]
    [h₁ : LawfulDialectMemPoison big] [h₂ : LawfulDialectMemPoison (dep.over e)] (hι : ι.Lawful)
    (hty : ∀ t : dep.Ty, validTy (ι.incl t) → validTy (d := dep.over e) (.inl t)) :
    LawfulDialectMemPoison (big.over (e.lift dep ι μ)) where
  poison_isRefinedBy {t} := match t with
    | .inl _ => fun hv p v hp => h₁.poison_isRefinedBy hv p v hp
    | .inr t => fun hv p v hp => h₂.poison_isRefinedBy (t := .inr t) hv p v hp
  propagates o hv hc := memPropagates_lift hι (h₂.propagates o (typesValid_lift hty hv) hc)
  returnsOnDefined o hv hc :=
    memReturnsOnDefined_lift hι (h₂.returnsOnDefined o (typesValid_lift hty hv) hc)

/-- The sum of a `big` lawful in its poison with memory and the lift of an
extension lawful in its poison with memory is lawful in its poison with
memory, when the inclusion is lawful and `e` accepts each type of `dep`
whose inclusion `big` accepts. -/
theorem sum_lawfulMemPoison [DialectSignature big] [DialectMemDenote big]
    [LawfulDialectMemPoison big] [LawfulDialectMemPoison (dep.over e)] (hι : ι.Lawful)
    (hty : ∀ t : dep.Ty, validTy (ι.incl t) → validTy (d := dep.over e) (.inl t)) :
    LawfulDialectMemPoison (big ⊞ e.lift dep ι μ) :=
  have := lawfulMemPoison (e := e) (big := big) (μ := μ) hι hty
  Dialect.sum.lawfulMemPoison fun _ h => h

end Dialect.lift

end Fir
