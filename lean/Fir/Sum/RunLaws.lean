import Fir.Sum.EffectLaws
import Fir.Execution.MemoryFinite
import Fir.Execution.Morphism

/-!
# Runs of a sum, op by op

Three facts that a run of a sum needs of its ops, each from the same fact of
its two sides, where a run names each memory of the base as the sum does:

* a base op tied to the set monad, which runs by its rule in the set monad
  and keeps the memories, is tied in the sum (`Dialect.sum.opLiftsSetM_inl`),
  since mapping its results to the sum's types commutes with the lift;
* the sum's ops have finitely many outcomes with memory when each side's do
  (`Dialect.sum.opsFinite`), since mapping the results keeps how many there
  are;
* a monad morphism that maps each side's semantics in one monad to its
  semantics in another maps the sum's (`Dialect.sum.mapsDenote`), since a
  morphism keeps `map`. So the tree of a run of the sum, which the modes
  walk, has the sum's run as its set when each side's tree has its side's.
-/

namespace Fir

namespace Dialect.sum

open Memory

variable {base e : Dialect} [TyDenote base.Ty] [TyDenote e.Ty]
  [DialectSignature base] [DialectSignature (base.over e)]

/-- A monad morphism that maps each side's semantics maps the sum's: a base
op's results are mapped to the sum's types, and a morphism keeps `map`. -/
theorem mapsDenote {m n : Type → Type} [Monad m] [Monad n] (φ : MonadMorphism m n)
    [DialectDenote base m] [DialectDenote base n] [DialectDenote (base.over e) m]
    [DialectDenote (base.over e) n] (h₁ : φ.MapsDenote (d := base))
    (h₂ : φ.MapsDenote (d := base.over e)) : φ.MapsDenote (d := base ⊞ e) where
  denote
    | .inl o, _ => (φ.map_map _ _).trans (congrArg _ (h₁.denote o _))
    | .inr o, args => h₂.denote o args
  exit
    | .inl o, _ => h₁.exit o _
    | .inr o, args => h₂.exit o args

variable [DialectEffects base] [DialectEffects (base.over e)] [DialectMemOver base e]
  [DialectMemDenote base] [DialectMemDenote (base.over e)]

/-- A base op tied to the set monad in the base is tied in the sum. -/
theorem opLiftsSetM_inl [DialectDenote base SetM] [DialectDenote (base.over e) SetM]
    {o : base.Op} (h : OpLiftsSetM o) : OpLiftsSetM (d := base ⊞ e) (.inl o) :=
  fun lay ρ _ =>
    ⟨(congrArg (HVector.toSum <$> ·) (h lay (ρ ∘ DialectMemOver.ofBase) _).1).trans
        ((MonadMorphism.liftState SetM _).map_map _ _).symm,
      (h lay (ρ ∘ DialectMemOver.ofBase) _).2⟩

/-- Mapping the results of a computation keeps finitely many outcomes. -/
theorem _root_.Fir.FinitelyMany.map {σ α β : Type} (f : α → β) {c : StateT σ SetM α}
    (h : FinitelyMany c) : FinitelyMany (f <$> c) := fun S => by
  obtain ⟨L, hL⟩ := h S
  refine ⟨L.map fun p => (f p.1, p.2), fun x hx => ?_⟩
  rcases (SetM.stateMap_apply f c S _).1 hx with ⟨a, S', ha, he⟩ | ⟨_, _, he⟩
  · cases he
    exact List.mem_map.2 ⟨_, hL _ ha, rfl⟩
  · cases he

variable [DialectCall base] [DialectCall (base.over e)] {N : Type} [DecidableEq N]
  (lay : N → MemLayout) (ρ : DialectEffects.Mem (base ⊞ e) → N)

/-- The sum's ops have finitely many outcomes with memory when the base's
do, where the run names each memory of the base as the sum does, and `e`'s
do. -/
theorem opsFinite
    (h₁ : letI := DialectMemDenote.denoteAt (d := base) lay (ρ ∘ DialectMemOver.ofBase)
      OpsFinite base N (unitsOf lay))
    (h₂ : letI := DialectMemDenote.denoteAt (d := base.over e) lay ρ
      OpsFinite (base.over e) N (unitsOf lay)) :
    letI := DialectMemDenote.denoteAt (d := base ⊞ e) lay ρ
    OpsFinite (base ⊞ e) N (unitsOf lay)
  | .inl o, hc, args =>
    ⟨fun ht => FinitelyMany.map _ ((h₁ o hc (HVector.ofSum args)).1 ht),
      (h₁ o hc (HVector.ofSum args)).2⟩
  | .inr o, hc, args => h₂ o hc args

end Dialect.sum

end Fir
