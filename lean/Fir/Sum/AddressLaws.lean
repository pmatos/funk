import Fir.Sum.EffectLaws
import Fir.Execution.AddressObligations

/-!
# The sum of dialects whose declarations cover addresses

A sum meets the obligations of the section on addresses and the declared
allocation when its two sides do (`Dialect.sum.lawfulAddresses`), as it
meets the effect obligations: each op has its own side's effects, an op of
the base runs by the base's rule where the run names the base's memories
as the sum does, and mapping its results to the sum's types changes no
memory. The condition is the one of the effect obligations: `e` accepts
every type that the base accepts.
-/

namespace Fir

namespace Dialect.sum

variable {base e : Dialect} [TyDenote base.Ty] [TyDenote e.Ty]
  [DialectSignature base] [DialectSignature (base.over e)]
  [DialectEffects base] [DialectEffects (base.over e)] [DialectMemOver base e]
  [DialectMemDenote base] [DialectMemDenote (base.over e)]
  [DialectCall base] [DialectCall (base.over e)]
  [DialectValidation base] [DialectValidation (base.over e)]

/-- Two dialects whose declarations cover addresses make a sum whose
declarations cover them, when `e` accepts every type that the base
accepts. -/
theorem lawfulAddresses [h₁ : LawfulDialectAddresses base]
    [h₂ : LawfulDialectAddresses (base.over e)]
    (hty : ∀ t : base.Ty, validTy t → validTy (d := base.over e) (.inl t)) :
    LawfulDialectAddresses (base ⊞ e) where
  exposesNot o hv hc _ _ lay ρ L x ha := by
    cases o with
    | inl o =>
      exact ownRuleHas_inl lay ρ L (fun f _ h => ExposesNot.map f h) (h₁.exposesNot o
        (typesValid_inl hv) hc lay _ L x (by rw [← MemSet.map_map]; exact ha))
    | inr o =>
      exact ownRuleHas_inr lay ρ L (h₂.exposesNot o (typesValid_inr hty hv) hc lay ρ L x ha)
  rebuildsNot o hv hc _ _ lay ρ L x ha := by
    cases o with
    | inl o =>
      exact ownRuleHas_inl lay ρ L (fun f _ h => RebuildsNot.map f h) (h₁.rebuildsNot o
        (typesValid_inl hv) hc lay _ L x (by rw [← MemSet.map_map]; exact ha))
    | inr o =>
      exact ownRuleHas_inr lay ρ L (h₂.rebuildsNot o (typesValid_inr hty hv) hc lay ρ L x ha)

end Dialect.sum

end Fir
