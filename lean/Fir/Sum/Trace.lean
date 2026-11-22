import Fir.Sum.EffectLaws
import Fir.Execution.TraceObligationLaws

/-!
# The traced semantics of a sum

A sum of dialects shows the events of both its sides. Its events are the
base's or `e`'s, and so are the world's answers to them; one event refines
another when both are of the same side and refine there. Each op of the sum
runs by its side's traced rule, as it runs by its side's rule with memory
(the section on the sum's memory): an op of the base takes its operands at
the base's types, where the run names each memory of the base as the sum
does, and its results become values of the sum's types. Each act that an
op of a side shows is the act of the sum on that side.

An op that runs, on its side, by its rule with memory, lifted onto the
memories of the traced state (`OpLiftsMem`), does so in the sum too: the
lift shows no act, so taking its acts to the sum's changes nothing, and
mapping the results to the sum's types commutes with the lift. So a sum of
two dialects whose traced semantics lift their semantics with memory lifts
its own (`Dialect.sum.liftsMem`).
-/

namespace Fir

open Memory

variable {E₁ A₁ E₂ A₂ : Type}

/-- An act of the left side, as an act of a sum. -/
def Act.inl (a : Act E₁ A₁) : Act (E₁ ⊕ E₂) (A₁ ⊕ A₂) := ⟨.inl a.event, .inl a.answer⟩

/-- An act of the right side, as an act of a sum. -/
def Act.inr (a : Act E₂ A₂) : Act (E₁ ⊕ E₂) (A₁ ⊕ A₂) := ⟨.inr a.event, .inr a.answer⟩

/-- Mapping the acts of a computation of the state layer, lifted onto the
memories of the traced state, changes nothing: it shows no act. -/
theorem TraceM.mapActs_liftMem {Mem : Type} {unit : Mem → Nat} {A B α : Type} (g : A → List B)
    (x : StateT (Memories Mem unit) SetM α) :
    TraceM.mapActs g (TraceM.liftMem (A := A) x) = TraceM.liftMem x := by
  funext s e
  apply propext
  constructor
  · rintro ⟨e', (⟨a, S', hx, rfl⟩ | ⟨r, hx, rfl⟩), rfl⟩
    · exact .inl ⟨a, S', hx, rfl⟩
    · exact .inr ⟨r, hx, rfl⟩
  · rintro (⟨a, S', hx, rfl⟩ | ⟨r, hx, rfl⟩)
    · exact ⟨_, .inl ⟨a, S', hx, rfl⟩, rfl⟩
    · exact ⟨_, .inr ⟨r, hx, rfl⟩, rfl⟩

namespace Dialect.sum

variable {base e : Dialect} [TyDenote base.Ty] [TyDenote e.Ty]
  [DialectSignature base] [DialectSignature (base.over e)]
  [DialectEffects base] [DialectEffects (base.over e)] [DialectMemOver base e]
  [DialectTrace base] [DialectTrace (base.over e)]

/-- The sum's traced semantics, wherever a run names its memories by `ρ`: its
events and their answers are either side's, and an op of `e` runs by `e`'s
traced rule and an op of the base by the base's, where the run names each
memory of the base as `ρ` names it in `e`, each act of a side an act of the
sum. -/
instance instDialectTrace : DialectTrace (base ⊞ e) where
  Event := DialectTrace.Event base ⊕ DialectTrace.Event (base.over e)
  Answer := DialectTrace.Answer base ⊕ DialectTrace.Answer (base.over e)
  IsRefinedBy := Sum.LiftRel DialectTrace.IsRefinedBy DialectTrace.IsRefinedBy
  traceAt lay ρ L :=
    letI := DialectTrace.traceAt (d := base) lay (ρ ∘ DialectMemOver.ofBase) L
    letI := DialectTrace.traceAt (d := base.over e) lay ρ L
    { denote
        | .inl o, args => TraceM.mapActs (fun a => [Act.inl a])
            (HVector.toSum <$> DialectDenote.denote o (HVector.ofSum args))
        | .inr o, args => TraceM.mapActs (fun a => [Act.inr a])
            (DialectDenote.denote (d := base.over e) o args)
      exit
        | .inl o, args => TraceM.mapActs (fun a => [Act.inl a])
            (DialectDenote.exit o (HVector.ofSum args))
        | .inr o, args => TraceM.mapActs (fun a => [Act.inr a])
            (DialectDenote.exit (d := base.over e) o args) }

/-- Refinement of the sum's events is transitive when each side's is. -/
theorem event_isRefinedBy_trans
    (h₁ : ∀ {a b c : DialectTrace.Event base}, a ⊑ b → b ⊑ c → a ⊑ c)
    (h₂ : ∀ {a b c : DialectTrace.Event (base.over e)}, a ⊑ b → b ⊑ c → a ⊑ c) :
    ∀ {a b c : DialectTrace.Event (base ⊞ e)}, a ⊑ b → b ⊑ c → a ⊑ c
  | _, _, _, .inl hab, .inl hbc => .inl (h₁ hab hbc)
  | _, _, _, .inr hab, .inr hbc => .inr (h₂ hab hbc)

variable [DialectMemDenote base] [DialectMemDenote (base.over e)] {N : Type} [DecidableEq N]
  (lay : N → MemLayout) (ρ : DialectEffects.Mem (base ⊞ e) → N) (L : RunItems)

/-- A base op that lifts its rule with memory in the base's traced semantics
lifts it in the sum's, where the run names each memory of the base as the
sum does. -/
theorem opLiftsMem_inl {o : base.Op} (h : OpLiftsMem lay (ρ ∘ DialectMemOver.ofBase) L o) :
    OpLiftsMem (d := base ⊞ e) lay ρ L (.inl o) := by
  letI := DialectMemDenote.denoteAt (d := base) lay (ρ ∘ DialectMemOver.ofBase) L
  letI := DialectTrace.traceAt (d := base) lay (ρ ∘ DialectMemOver.ofBase) L
  intro args
  refine ⟨?_, ?_⟩
  · show TraceM.liftMem (HVector.toSum <$> _) =
      TraceM.mapActs _ (HVector.toSum <$> DialectDenote.denote o (HVector.ofSum args))
    refine (((congrArg (fun x => TraceM.mapActs (fun a => [Act.inl a]) (HVector.toSum <$> x))
      (h (HVector.ofSum args)).1).symm.trans (congrArg (TraceM.mapActs _)
        ((MonadMorphism.traceMem N (unitsOf lay) (DialectTrace.Acts base)).map_map _ _).symm)).trans
      (TraceM.mapActs_liftMem _ _)).symm
  · show _ = TraceM.mapActs _ (DialectDenote.exit o (HVector.ofSum args))
    rw [← (h (HVector.ofSum args)).2, TraceM.mapActs_liftMem]
    rfl

/-- An op of `e` that lifts its rule with memory in `e`'s traced semantics
lifts it in the sum's. -/
theorem opLiftsMem_inr {o : e.Op} (h : OpLiftsMem (d := base.over e) lay ρ L o) :
    OpLiftsMem (d := base ⊞ e) lay ρ L (.inr o) := by
  letI := DialectMemDenote.denoteAt (d := base.over e) lay ρ L
  letI := DialectTrace.traceAt (d := base.over e) lay ρ L
  intro args
  refine ⟨?_, ?_⟩
  · show _ = TraceM.mapActs _ (DialectDenote.denote (d := base.over e) o args)
    rw [← (h args).1, TraceM.mapActs_liftMem]
    rfl
  · show _ = TraceM.mapActs _ (DialectDenote.exit (d := base.over e) o args)
    rw [← (h args).2, TraceM.mapActs_liftMem]
    rfl

/-- Each op of the sum lifts its rule with memory when each op of each side
does on its side. -/
theorem opLiftsMem (h₁ : ∀ o : base.Op, OpLiftsMem lay (ρ ∘ DialectMemOver.ofBase) L o)
    (h₂ : ∀ o : e.Op, OpLiftsMem (d := base.over e) lay ρ L o) :
    ∀ op, OpLiftsMem (d := base ⊞ e) lay ρ L op
  | .inl o => opLiftsMem_inl lay ρ L (h₁ o)
  | .inr o => opLiftsMem_inr lay ρ L (h₂ o)

/-- A sum of two dialects whose traced semantics lift their semantics with
memory lifts its own. -/
theorem liftsMem [DecidableEq base.Ty] [DecidableEq e.Ty] [DialectCall base]
    [DialectCall (base.over e)] [LiftsMem base] [LiftsMem (base.over e)] :
    LiftsMem (base ⊞ e) :=
  ⟨fun lay ρ L => by
    letI := DialectMemDenote.denoteAt (d := base ⊞ e) lay ρ L
    letI := DialectTrace.traceAt (d := base ⊞ e) lay ρ L
    have h := opLiftsMem lay ρ L (LiftsMem.opLiftsMem lay (ρ ∘ DialectMemOver.ofBase) L)
      (LiftsMem.opLiftsMem (d := base.over e) lay ρ L)
    exact ⟨fun op args => (h op args).1, fun op args => (h op args).2⟩⟩

end Dialect.sum

end Fir
