import Fir.Sum.LiftEffectLaws
import Fir.Execution.MemoryOpRefine

/-!
# The sum and the lift of dialects lawful in their monotonicity

A sum is lawful in its monotonicity when its two sides are
(`Dialect.sum.lawfulMonotone`), and so is the lift of an extension that is,
through a lawful inclusion (`Dialect.lift.lawfulMonotone`), under the
conditions on types that make them lawful for poison. Each op runs by its
own side's rule with memory, where the run names that side's memories
through the side's memory map (the sections on the sum and the lift of
dialects lawful in their effects), and only the values change the type they
are seen at:

* operands of the sum's types refine others exactly when they do at the
  side's types, so the side's rule sees operands that refine others;
* mapping the results by a map that keeps refinement keeps refinement of
  computations with memory: moving values to the sum's types does, and so
  does crossing a lawful inclusion up.

Neither needs a semantics in the set monad, so a side whose ops touch
memory may take part.
-/

namespace Fir

namespace Dialect.sum

variable {base e : Dialect} [TyDenote base.Ty] [TyDenote e.Ty] [TyRefinement base.Ty]
  [TyRefinement e.Ty] [DialectSignature base] [DialectSignature (base.over e)]
  [DialectEffects base] [DialectEffects (base.over e)] [DialectMemOver base e]
  [DialectMemDenote base] [DialectMemDenote (base.over e)]

/-- A base op monotone with memory in the base is monotone with memory in
the sum. -/
theorem memMonotone_inl {o : base.Op} (h : MemMonotone o) :
    MemMonotone (d := base ⊞ e) (.inl o) := fun lay ρ args args' hargs =>
  have hm := h lay (ρ ∘ DialectMemOver.ofBase) (HVector.ofSum args) (HVector.ofSum args')
    ((forall₂_refines_ofSum args args').2 hargs)
  ⟨fun hn => StateRefinedBy.map HVector.toSum (fun {a a'} ha => by
      rw [← forall₂_refines_ofSum, HVector.ofSum_toSum, HVector.ofSum_toSum]
      exact ha) (hm.1 hn), hm.2⟩

variable [DialectCall base] [DialectCall (base.over e)]
  [DialectValidation base] [DialectValidation (base.over e)]

/-- Two dialects lawful in their monotonicity make a sum lawful in its
monotonicity, when `e` accepts every type that the base accepts. -/
theorem lawfulMonotone [h₁ : LawfulDialectMonotone base]
    [h₂ : LawfulDialectMonotone (base.over e)]
    (hty : ∀ t : base.Ty, validTy t → validTy (d := base.over e) (.inl t)) :
    LawfulDialectMonotone (base ⊞ e) where
  monotone
    | .inl o, hv, hc => memMonotone_inl (h₁.monotone o (typesValid_inl hv) hc)
    | .inr o, hv, hc => h₂.monotone o (typesValid_inr hty hv) hc

end Dialect.sum

namespace Dialect.lift

variable {e dep big : Dialect} [TyDenote dep.Ty] [TyDenote big.Ty] [TyDenote e.Ty]
  [TyPoison dep.Ty] [TyPoison big.Ty] [TyPoison e.Ty] [TyRefinement dep.Ty] [TyRefinement big.Ty]
  [TyRefinement e.Ty] {ι : TyIncl dep.Ty big.Ty} [DialectSignature (dep.over e)]
  [DialectEffects dep] [DialectEffects big] [DialectEffects (dep.over e)] [DialectMemOver dep e]
  [DialectMemDenote (dep.over e)] {μ : DialectEffects.Mem dep → DialectEffects.Mem big}

/-- An op of `e` monotone with memory over `dep` is monotone with memory in
the lift, when the inclusion is lawful. -/
theorem memMonotone_lift (hι : ι.Lawful) {o : e.Op} (h : MemMonotone (d := dep.over e) o) :
    MemMonotone (d := big.over (e.lift dep ι μ)) o := fun lay ρ args args' hargs =>
  have hm := h lay (ρ ∘ liftMem μ) (HVector.down (incl e ι μ) args)
    (HVector.down (incl e ι μ) args')
    ((HVector.forall₂_down (incl_lawful e μ hι).isRefinedBy_up args args').2 hargs)
  ⟨fun hn => StateRefinedBy.map (HVector.up (incl e ι μ))
    (fun {a a'} ha => (HVector.forall₂_up (incl_lawful e μ hι).isRefinedBy_up a a').2 ha)
    (hm.1 hn), hm.2⟩

variable [DialectCall (dep.over e)] [DialectValidation big] [DialectValidation (dep.over e)]

/-- The lift of an extension lawful in its monotonicity is lawful in its
monotonicity, when the inclusion is lawful and `e` accepts each type of
`dep` whose inclusion `big` accepts. -/
theorem lawfulMonotone [h : LawfulDialectMonotone (dep.over e)] (hι : ι.Lawful)
    (hty : ∀ t : dep.Ty, validTy (ι.incl t) → validTy (d := dep.over e) (.inl t)) :
    LawfulDialectMonotone (big.over (e.lift dep ι μ)) where
  monotone o hv hc := memMonotone_lift hι (h.monotone o (typesValid_lift hty hv) hc)

variable [DialectSignature big] [DialectCall big] [DialectMemDenote big]

/-- The sum of a `big` lawful in its monotonicity and the lift of an
extension lawful in its monotonicity is lawful in its monotonicity, when
the inclusion is lawful and `e` accepts each type of `dep` whose inclusion
`big` accepts. -/
theorem sum_lawfulMonotone [LawfulDialectMonotone big] [LawfulDialectMonotone (dep.over e)]
    (hι : ι.Lawful)
    (hty : ∀ t : dep.Ty, validTy (ι.incl t) → validTy (d := dep.over e) (.inl t)) :
    LawfulDialectMonotone (big ⊞ e.lift dep ι μ) :=
  have := lawfulMonotone (e := e) (big := big) (μ := μ) hι hty
  Dialect.sum.lawfulMonotone fun _ h => h

end Dialect.lift

end Fir
