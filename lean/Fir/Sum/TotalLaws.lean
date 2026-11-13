import Fir.Sum.LiftEffectLaws
import Fir.Execution.MemoryTotal

/-!
# The sum and the lift of dialects lawful in their totality

A sum is lawful in its totality when its two sides are
(`Dialect.sum.lawfulTotal`), and so is the lift of an extension that is
(`Dialect.lift.lawfulTotal`), under the conditions on types that make them
lawful for poison. Each op runs by its own side's rule with memory, where
the run names that side's memories through the side's memory map (the
sections on the sum and the lift of dialects lawful in their effects), and
only its results change the type they are seen at. Mapping the results of
a computation keeps an outcome, so an op that has an outcome from any
memories in its side has one in the sum and in the lift. Neither needs a
semantics in the set monad, so a side whose ops touch memory may take part.
-/

namespace Fir

namespace Dialect.sum

variable {base e : Dialect} [TyDenote base.Ty] [TyDenote e.Ty]
  [DialectSignature base] [DialectSignature (base.over e)]
  [DialectEffects base] [DialectEffects (base.over e)] [DialectMemOver base e]
  [DialectMemDenote base] [DialectMemDenote (base.over e)]

/-- A base op total with memory in the base is total with memory in the
sum. -/
theorem memTotal_inl {o : base.Op} (h : MemTotal o) : MemTotal (d := base ⊞ e) (.inl o) :=
  fun lay ρ => ownRuleHas_inl lay ρ (fun f _ h => HasOutcome.map f h)
    (h lay (ρ ∘ DialectMemOver.ofBase))

variable [DialectCall base] [DialectCall (base.over e)]
  [DialectValidation base] [DialectValidation (base.over e)]

/-- Two dialects lawful in their totality make a sum lawful in its
totality, when `e` accepts every type that the base accepts. -/
theorem lawfulTotal [h₁ : LawfulDialectTotal base] [h₂ : LawfulDialectTotal (base.over e)]
    (hty : ∀ t : base.Ty, validTy t → validTy (d := base.over e) (.inl t)) :
    LawfulDialectTotal (base ⊞ e) where
  total
    | .inl o, hv, hc => memTotal_inl (h₁.total o (typesValid_inl hv) hc)
    | .inr o, hv, hc => h₂.total o (typesValid_inr hty hv) hc

end Dialect.sum

namespace Dialect.lift

variable {e dep big : Dialect} [TyDenote dep.Ty] [TyDenote big.Ty] [TyDenote e.Ty]
  {ι : TyIncl dep.Ty big.Ty} [DialectSignature (dep.over e)]
  [DialectEffects dep] [DialectEffects big] [DialectEffects (dep.over e)] [DialectMemOver dep e]
  [DialectMemDenote (dep.over e)] {μ : DialectEffects.Mem dep → DialectEffects.Mem big}

/-- An op of `e` total with memory over `dep` is total with memory in the
lift. -/
theorem memTotal_lift {o : e.Op} (h : MemTotal (d := dep.over e) o) :
    MemTotal (d := big.over (e.lift dep ι μ)) o :=
  fun lay ρ => ownRuleHas_lift lay ρ (fun f _ h => HasOutcome.map f h) (h lay (ρ ∘ liftMem μ))

variable [DialectCall (dep.over e)] [DialectValidation big] [DialectValidation (dep.over e)]

/-- The lift of an extension lawful in its totality is lawful in its
totality, when `e` accepts each type of `dep` whose inclusion `big`
accepts. -/
theorem lawfulTotal [h : LawfulDialectTotal (dep.over e)]
    (hty : ∀ t : dep.Ty, validTy (ι.incl t) → validTy (d := dep.over e) (.inl t)) :
    LawfulDialectTotal (big.over (e.lift dep ι μ)) where
  total o hv hc := memTotal_lift (h.total o (typesValid_lift hty hv) hc)

variable [DialectSignature big] [DialectCall big] [DialectMemDenote big]

/-- The sum of a `big` lawful in its totality and the lift of an extension
lawful in its totality is lawful in its totality, when `e` accepts each type
of `dep` whose inclusion `big` accepts. -/
theorem sum_lawfulTotal [LawfulDialectTotal big] [LawfulDialectTotal (dep.over e)]
    (hty : ∀ t : dep.Ty, validTy (ι.incl t) → validTy (d := dep.over e) (.inl t)) :
    LawfulDialectTotal (big ⊞ e.lift dep ι μ) :=
  have := lawfulTotal (e := e) (big := big) (μ := μ) hty
  Dialect.sum.lawfulTotal fun _ h => h

end Dialect.lift

end Fir
