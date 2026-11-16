import Fir.Execution.TraceRuns

/-!
# A dialect's traced runs

A dialect says what its events and their answers are, how one event refines
another, and gives its ops a semantics in the traced layer, wherever a run
names its memories. The traced runs of a function are the runs of the
interpreter in the traced layer of marked traces, from the empty memories,
where each op that runs by the dialect's rule, a terminator among them,
first shows a step. A call shows no step of its own: the ops of its callee
show theirs. Erasing the steps maps the traced runs to the runs by the
dialect's rules alone.

A dialect whose ops show no event has, in the traced layer, its semantics
with memory, lifted: its traced runs then show no act and end as its runs
with memory, and every theorem about the refinement of its runs with memory
holds of its traced runs. M0's dialects show no event, but none has a
traced semantics yet; once one has a traced semantics that lifts its
semantics with memory, its tests keep their results by this theorem.
-/

namespace Fir

open Memory

variable {A : Type}

/-- A dialect's events and their answers, how one event refines another, and
its semantics in the traced layer, where a run names the dialect's memory
`x` as `ρ x`, whose layout entry is `lay (ρ x)`. -/
class DialectTrace (d : Dialect) [TyDenote d.Ty] [DialectSignature d] [DialectEffects d] where
  /-- The events that the dialect's ops show. -/
  Event : Type
  /-- The world's answers to them. -/
  Answer : Type
  /-- `IsRefinedBy e e'`: the event `e'` refines the event `e`. -/
  IsRefinedBy : Event → Event → Prop
  /-- The semantics of each op in the traced layer. -/
  traceAt : {N : Type} → [DecidableEq N] → (lay : N → MemLayout) →
    (ρ : DialectEffects.Mem d → N) →
    DialectDenote d (TraceM (Act Event Answer) (Memories N (unitsOf lay)))

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectEffects d] [DialectTrace d]

instance : HRefinement (DialectTrace.Event d) (DialectTrace.Event d) :=
  ⟨DialectTrace.IsRefinedBy⟩

/-- The acts of the dialect's traces: its events with their answers. -/
abbrev DialectTrace.Acts (d : Dialect) [TyDenote d.Ty] [DialectSignature d] [DialectEffects d]
    [DialectTrace d] : Type :=
  Act (DialectTrace.Event d) (DialectTrace.Answer d)

/-- A step of the run, in the traced layer of marked traces. -/
def TraceM.tick {σ : Type} : TraceM (Step A) σ Unit := fun s e => e = .ok ((), [.tick], s)

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N)

/-- The dialect's semantics in the traced layer of marked traces: each op
shows a step, then runs by the dialect's rule, each act of its traces an act
of the marked trace. -/
@[instance_reducible] def DialectTrace.stepAt :
    DialectDenote d (TraceM (Step (DialectTrace.Acts d)) (Memories N (unitsOf lay))) :=
  letI := DialectTrace.traceAt (d := d) lay ρ
  { denote op args := TraceM.tick >>= fun _ =>
      TraceM.mapActs (fun a => [.act a]) (DialectDenote.denote op args)
    exit op args := TraceM.tick >>= fun _ =>
      TraceM.mapActs (fun a => [.act a]) (DialectDenote.exit op args) }

variable [DecidableEq d.Ty] [DialectCall d]

/-- The traced runs of the function `f` of the module `M`, where a run names
the dialect's memory `x` as `ρ x`, whose layout entry is `lay (ρ x)`: its run
in the traced layer of marked traces, each op that runs by the dialect's
rule showing a step before it, from the empty memories, at each budget, on
each argument vector of its parameter types. An observer sees the acts of the
trace and what it returns. -/
def Func.traceRuns (M : Module d) (f : Func d) :
    FuncTraceRuns (HVector toType (f.params.map (·.2))) (DialectTrace.Acts d) (List (DVal d)) :=
  letI := DialectTrace.stepAt (d := d) lay ρ
  fun args fuel e => ∃ e',
    (f.run M (m := TraceM (Step (DialectTrace.Acts d)) (Memories N (unitsOf lay))) args fuel).run
      Memories.empty e' ∧ e = e'.map fun p => (p.1, p.2.1)

/-- Erasing the steps of the traced runs of a function gives its runs in the
traced layer by the dialect's rules alone. -/
theorem Func.run_eraseSteps (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    letI := DialectTrace.stepAt (d := d) lay ρ
    letI := DialectTrace.traceAt (d := d) lay ρ
    ((MonadMorphism.mapActs (Memories N (unitsOf lay)) Step.acts).except Stuck).map
        (f.run M (m := TraceM (Step (DialectTrace.Acts d)) (Memories N (unitsOf lay))) args fuel) =
      f.run M (m := TraceM (DialectTrace.Acts d) (Memories N (unitsOf lay))) args fuel := by
  letI := DialectTrace.stepAt (d := d) lay ρ
  letI := DialectTrace.traceAt (d := d) lay ρ
  have hstep : ∀ {α : Type} (x : TraceM (DialectTrace.Acts d) (Memories N (unitsOf lay)) α),
      TraceM.mapActs Step.acts (TraceM.tick >>= fun _ => TraceM.mapActs (fun a => [.act a]) x) = x := by
    intro α x
    rw [TraceM.mapActs_bind]
    have htick : TraceM.mapActs (σ := Memories N (unitsOf lay)) (A := Step (DialectTrace.Acts d))
        Step.acts TraceM.tick = pure () := by
      funext s e
      exact propext ⟨fun ⟨_, h, he⟩ => by cases (h : _ = _); exact he, fun h => ⟨_, rfl, h⟩⟩
    rw [htick, TraceM.pure_bind, TraceM.mapActs_mapActs]
    exact TraceM.mapActs_singleton x
  have hmaps : (MonadMorphism.mapActs (Memories N (unitsOf lay))
      (Step.acts (A := DialectTrace.Acts d))).MapsDenote (d := d) := by
    constructor <;> intro op args
    · exact hstep (DialectDenote.denote (m := TraceM (DialectTrace.Acts d) _) op args)
    · exact hstep (DialectDenote.exit (m := TraceM (DialectTrace.Acts d) _) op args)
  exact Func.run_map hmaps (MonadMorphism.mapActs_mapsFrame _) M f args fuel

/-- A dialect whose ops show no event: wherever a run names its memories,
its semantics in the traced layer is its semantics with memory, lifted. -/
class LiftsMem (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
    [DialectCall d] [DialectEffects d] [DialectMemDenote d] [DialectTrace d] : Prop where
  lifts : ∀ {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N),
    letI := DialectMemDenote.denoteAt (d := d) lay ρ
    letI := DialectTrace.traceAt (d := d) lay ρ
    (MonadMorphism.trace (DialectTrace.Acts d) (Memories N (unitsOf lay))).MapsDenote (d := d)

/-- The traced runs of a function of a dialect whose ops show no event show
no act, and end as its runs with memory. -/
theorem Func.traceRuns_noActs [DialectMemDenote d] [LiftsMem d] (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    (f.traceRuns lay ρ M args fuel).NoActs (f.memRuns lay ρ M args fuel) := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ
  letI := DialectTrace.traceAt (d := d) lay ρ
  letI := DialectTrace.stepAt (d := d) lay ρ
  have hY : TraceM.mapActs Step.acts
      ((f.run M (m := TraceM (Step (DialectTrace.Acts d)) (Memories N (unitsOf lay))) args fuel).run) =
      TraceM.lift (f.run M (m := StateT (Memories N (unitsOf lay)) SetM) args fuel).run :=
    (congrArg ExceptT.run (Func.run_eraseSteps lay ρ M f args fuel)).trans
      (congrArg ExceptT.run (Func.run_map (LiftsMem.lifts lay ρ) MonadMorphism.trace_mapsFrame
        M f args fuel)).symm
  have hfwd : ∀ e', ((f.run M (m := TraceM (Step (DialectTrace.Acts d)) (Memories N (unitsOf lay))) args fuel).run
        Memories.empty e') → TraceM.lift (A := DialectTrace.Acts d)
          (f.run M (m := StateT (Memories N (unitsOf lay)) SetM) args fuel).run Memories.empty
          (e'.mapActs Step.acts) := fun e' h => hY ▸ ⟨e', h, rfl⟩
  have hbwd : ∀ e, TraceM.lift (A := DialectTrace.Acts d)
      (f.run M (m := StateT (Memories N (unitsOf lay)) SetM) args fuel).run Memories.empty e →
      ∃ e', ((f.run M (m := TraceM (Step (DialectTrace.Acts d)) (Memories N (unitsOf lay))) args
          fuel).run Memories.empty e') ∧ e = e'.mapActs Step.acts := fun e h => (hY ▸ h :)
  refine ⟨?_, ?_, fun x => ⟨?_, ?_⟩, fun r => ⟨?_, ?_⟩⟩
  · rintro x mt ⟨(⟨_, _⟩ | ⟨_, _, _⟩), h, he⟩ <;> cases he
    rcases hfwd _ h with ⟨_, _, _, he⟩ | ⟨_, _, he⟩
    · simp only [TraceEnd.mapActs, Except.ok.injEq, Prod.mk.injEq] at he
      exact he.2.1
    · cases he
  · rintro r mt ⟨(⟨_, _⟩ | ⟨_, _, _⟩), h, he⟩ <;> cases he
    rcases hfwd _ h with ⟨_, _, _, he⟩ | ⟨_, _, he⟩
    · cases he
    · simp only [TraceEnd.mapActs, Except.error.injEq, Prod.mk.injEq] at he
      exact he.2
  · rintro ⟨mt, (⟨_, _⟩ | ⟨_, _, _⟩), h, he⟩ <;> cases he
    rcases hfwd _ h with ⟨_, _, hz, he⟩ | ⟨_, _, he⟩
    · simp only [TraceEnd.mapActs, Except.ok.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, -, -⟩ := he
      exact .inl ⟨_, hz, rfl⟩
    · cases he
  · rintro (⟨⟨_, S'⟩, hz, he⟩ | ⟨_, _, he⟩) <;> cases (he : _ = _)
    obtain ⟨(⟨_, _⟩ | ⟨_, mt, _⟩), h, he⟩ := hbwd _ (.inl ⟨_, S', hz, rfl⟩)
    · cases he
    · simp only [TraceEnd.mapActs, Except.ok.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, -, -⟩ := he
      exact ⟨mt, _, h, rfl⟩
  · rintro ⟨mt, (⟨_, _⟩ | ⟨_, _, _⟩), h, he⟩ <;> cases he
    rcases hfwd _ h with ⟨_, _, _, he⟩ | ⟨_, hz, he⟩
    · cases he
    · simp only [TraceEnd.mapActs, Except.error.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      exact .inr ⟨_, hz, rfl⟩
  · rintro (⟨_, _, he⟩ | ⟨_, hz, he⟩) <;> cases (he : _ = _)
    obtain ⟨(⟨_, mt⟩ | ⟨_, _, _⟩), h, he⟩ := hbwd _ (.inr ⟨_, hz, rfl⟩)
    · simp only [TraceEnd.mapActs, Except.error.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      exact ⟨mt, _, h, rfl⟩
    · cases he

/-- The traced observable behaviour of a function of a dialect whose ops show
no event is its observable behaviour with memory, each outcome with an empty
trace. So refinement of its traced runs is refinement of its runs with
memory, and every theorem on the latter holds of the former. -/
theorem Func.traceObservable_traceRuns [DialectMemDenote d] [LiftsMem d] (M : Module d)
    (f : Func d) (args : HVector toType (f.params.map (·.2))) :
    traceObservable (f.traceRuns lay ρ M args) = .ofBehaviour (observable (f.memRuns lay ρ M args)) :=
  traceObservable_of_noActs (Func.traceRuns_noActs lay ρ M f args)

end Fir
