import Fir.Sum.PoisonLaws
import Fir.Execution.MemoryObligationLaws

/-!
# The sum of dialects lawful in their effects is lawful in its effects

A sum meets the effect obligations when its two sides do
(`Dialect.sum.lawfulEffects`). Each op of the sum has its own side's effects
(the section on the sum of dialects), so each op meets them as an op of its
own side: an op of the base runs by the base's rule on the same values,
which only change the type they are seen at, and an op of `e` runs by `e`'s
rule over the base. Moving a vector between the base's types and the sum's
keeps which values are poison, and a base op ends in UB in the sum exactly
when it does in the base. The one condition is the one for poison: `e`
accepts every type that the base accepts.

The sum's semantics with memory runs a base op by the base's at the run's
naming composed with `ofBase`, and an op of `e` by `e`'s. So a base op meets
the memory obligations in the sum because it meets them in the base at that
naming: its declaration, renamed by `ofBase` and then by the run's naming,
is renamed by the composite, and mapping its results to the sum's types
changes no memory.
-/

namespace Fir

section
variable {base e : Dialect} [TyDenote base.Ty] [TyDenote e.Ty] [TyPoison base.Ty] [TyPoison e.Ty]

/-- A vector holds poison at the sum's types exactly when it does at the
base's. -/
theorem HVector.any_toSum : ∀ {ts : List base.Ty} (xs : HVector toType ts),
    (HVector.toSum (e := e) xs).Any TyPoison.IsPoison ↔ xs.Any TyPoison.IsPoison
  | [], .nil => Iff.rfl
  | _ :: _, .cons _ xs => or_congr Iff.rfl (HVector.any_toSum xs)

end

namespace Dialect.sum

open Memory

section

/-! # Memory -/

variable {base e : Dialect} [TyDenote base.Ty] [TyDenote e.Ty]
  [DialectSignature base] [DialectSignature (base.over e)]
  [DialectEffects base] [DialectEffects (base.over e)] [DialectMemOver base e]

/-- The sum's semantics with memory, wherever a run names its memories by
`ρ`: an op of `e` runs by `e`'s rule, and an op of the base by the base's,
where the run names each memory of the base as `ρ` names it in `e`. -/
instance instDialectMemDenote [DialectMemDenote base] [DialectMemDenote (base.over e)] :
    DialectMemDenote (base ⊞ e) where
  denoteAt unit ρ :=
    letI := DialectMemDenote.denoteAt (d := base) unit (ρ ∘ DialectMemOver.ofBase)
    letI := DialectMemDenote.denoteAt (d := base.over e) unit ρ
    instDialectDenote

variable [DialectMemDenote base] [DialectMemDenote (base.over e)] {N : Type} [DecidableEq N]
  (unit : N → Nat) (ρ : DialectEffects.Mem (base ⊞ e) → N)
  {P : {α : Type} → StateT (Memories N unit) SetM α → Prop}

/-- A property that mapping the results keeps holds of what a base op runs
by its own rule in the sum, when it holds in the base, where the run names
each memory of the base as the sum does. -/
theorem ownRuleHas_inl (hP : ∀ {α β : Type} (f : α → β) (c : StateT (Memories N unit) SetM α),
      P c → P (f <$> c)) {o : base.Op}
    (h : OwnRuleHas unit (ρ ∘ DialectMemOver.ofBase) P o) :
    OwnRuleHas (d := base ⊞ e) unit ρ P (.inl o) := fun args =>
  ⟨fun ht => hP _ _ ((h (HVector.ofSum args)).1 ht), fun ht => (h (HVector.ofSum args)).2 ht⟩

/-- What an op of `e` runs by its own rule in the sum is what it runs in
`e`. -/
theorem ownRuleHas_inr {o : e.Op} (h : OwnRuleHas (d := base.over e) unit ρ P o) :
    OwnRuleHas (d := base ⊞ e) unit ρ P (.inr o) := h

end

variable {base e : Dialect} [TyDenote base.Ty] [TyDenote e.Ty]
  [DialectSignature base] [DialectSignature (base.over e)]
  [DialectDenote base SetM] [DialectDenote (base.over e) SetM]

/-- A base op that never ends in UB in the base never does in the sum. -/
theorem neverUB_inl {o : base.Op} (h : NeverUB o) : NeverUB (d := base ⊞ e) (.inl o) :=
  fun args r =>
    ⟨fun ht hden => by
      rcases (map_toSum _ _).1 hden with ⟨a, -, he⟩ | ⟨r', hr, he⟩
      · cases he
      · cases he
        exact (h (HVector.ofSum args) r).1 ht hr,
    fun ht hex => (h (HVector.ofSum args) r).2 ht hex⟩

variable [TyPoison base.Ty] [TyPoison e.Ty]

/-- A base op that makes no poison in the base makes none in the sum. -/
theorem makesNoPoison_inl {o : base.Op} (h : MakesNoPoison o) :
    MakesNoPoison (d := base ⊞ e) (.inl o) := fun ht args hnp rs hden => by
  rcases (map_toSum _ _).1 hden with ⟨a, ha, he⟩ | ⟨r, -, he⟩
  · cases he
    exact fun hp => h ht _ (fun hd => hnp ((HVector.any_ofSum args).1 hd)) a ha
      ((HVector.any_toSum a).1 hp)
  · cases he

variable [DialectEffects base] [DialectEffects (base.over e)] [DialectMemOver base e]

variable [DialectMemDenote base] [DialectMemDenote (base.over e)]

variable [DialectCall base] [DialectCall (base.over e)]
  [DialectValidation base] [DialectValidation (base.over e)]

/-- Two dialects lawful in their effects make a sum lawful in its effects,
when `e` accepts every type that the base accepts: each op meets the
obligations as its own side's op. A base op meets the memory obligations
where the run names the base's memories as the sum does. -/
theorem lawfulEffects [h₁ : LawfulDialectEffects base] [h₂ : LawfulDialectEffects (base.over e)]
    (hty : ∀ t : base.Ty, validTy t → validTy (d := base.over e) (.inl t)) :
    LawfulDialectEffects (base ⊞ e) where
  neverUB
    | .inl o, hv, hc, hu => neverUB_inl (h₁.neverUB o (typesValid_inl hv) hc hu)
    | .inr o, hv, hc, hu => h₂.neverUB o (typesValid_inr hty hv) hc hu
  makesNoPoison
    | .inl o, hv, hc, hp => makesNoPoison_inl (h₁.makesNoPoison o (typesValid_inl hv) hc hp)
    | .inr o, hv, hc, hp => h₂.makesNoPoison o (typesValid_inr hty hv) hc hp
  notControl
    | .inl o, hc => h₁.notControl o hc
    | .inr o, hc => h₂.notControl o hc
  writesNot o hv hc _ _ unit ρ x hw := by
    cases o with
    | inl o =>
      exact ownRuleHas_inl unit ρ (fun f _ h => WritesNot.map f h) (h₁.writesNot o
        (typesValid_inl hv) hc unit _ x (by rw [← MemSet.map_map]; exact hw))
    | inr o => exact ownRuleHas_inr unit ρ (h₂.writesNot o (typesValid_inr hty hv) hc unit ρ x hw)
  readsNot o hv hc _ _ unit ρ x hr := by
    cases o with
    | inl o =>
      exact ownRuleHas_inl unit ρ (fun f _ h => ReadsNot.map f h) (h₁.readsNot o
        (typesValid_inl hv) hc unit _ x (by rw [← MemSet.map_map]; exact hr))
    | inr o => exact ownRuleHas_inr unit ρ (h₂.readsNot o (typesValid_inr hty hv) hc unit ρ x hr)
  allocatesNot o hv hc _ _ unit ρ x ha := by
    cases o with
    | inl o =>
      exact ownRuleHas_inl unit ρ (fun f _ h => AllocatesNot.map f h) (h₁.allocatesNot o
        (typesValid_inl hv) hc unit _ x (by rw [← MemSet.map_map]; exact ha))
    | inr o =>
      exact ownRuleHas_inr unit ρ (h₂.allocatesNot o (typesValid_inr hty hv) hc unit ρ x ha)

end Dialect.sum

end Fir
