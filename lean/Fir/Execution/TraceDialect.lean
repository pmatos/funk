import Fir.Execution.TraceRuns
import Fir.Execution.TraceWorld
import Fir.Execution.ObserveEnd
import Fir.Execution.MemoryRuns

/-!
# A dialect's traced runs

A dialect says what its events and their answers are, how one event refines
another, and gives its ops a semantics in the traced layer, wherever a run
names its memories and whatever items it gives each op. The traced runs of
a function are the runs of the interpreter in the traced layer of marked
traces, from the memories that hold the run's starting allocations, with
nothing escaped,
where each op that runs by the dialect's rule, a terminator among them,
first shows a step. A call shows no step of its own: the ops of its callee
show theirs. Erasing the steps maps the traced runs to the runs by the
dialect's rules alone. An observer sees the acts of the trace and, at a
return, the end of the return: the returned values, the memories and what
escaped (`Fir.Execution.ObserveEnd`). The spec's traced runs compare no
addresses at the end of a return (`Func.observedRuns`).

A dialect whose ops show no event has, in the traced layer, its semantics
with memory, lifted onto the memories of the traced state: its traced runs
then show no act, nothing escapes, and they end as its runs with memory,
each return seen at its end. M0's dialects show no event and return no
pointer. The core and CoreGpu have a traced semantics that lifts their
semantics with memory (`Fir.Core.Trace`, `Fir.Gpu.Trace`), so their tests
keep their results by this theorem and `End.isRefinedBy_iff_vals`.
-/

namespace Fir

open Memory

variable {A : Type}

/-- A dialect's events and their answers, how one event refines another, and
its semantics in the traced layer, where a run names the dialect's memory
`x` as `ρ x`, whose layout entry is `lay (ρ x)`, and gives the items `L`. -/
class DialectTrace (d : Dialect) [TyDenote d.Ty] [DialectSignature d] [DialectEffects d] where
  /-- The events that the dialect's ops show. -/
  Event : Type
  /-- The world's answers to them. -/
  Answer : Type
  /-- `IsRefinedBy e e'`: the event `e'` refines the event `e`. -/
  IsRefinedBy : Event → Event → Prop
  /-- The semantics of each op in the traced layer. -/
  traceAt : {N : Type} → [DecidableEq N] → (lay : N → MemLayout) →
    (ρ : DialectEffects.Mem d → N) → (L : RunItems) →
    DialectDenote d (TraceM (Act Event Answer) (TraceState N (unitsOf lay)))

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
  (L : RunItems)

/-- The dialect's semantics in the traced layer of marked traces: each op
shows a step, then runs by the dialect's rule, each act of its traces an act
of the marked trace. -/
@[instance_reducible] def DialectTrace.stepAt :
    DialectDenote d (TraceM (Step (DialectTrace.Acts d)) (TraceState N (unitsOf lay))) :=
  letI := DialectTrace.traceAt (d := d) lay ρ L
  { denote op args := TraceM.tick >>= fun _ =>
      TraceM.mapActs (fun a => [.act a]) (DialectDenote.denote op args)
    exit op args := TraceM.tick >>= fun _ =>
      TraceM.mapActs (fun a => [.act a]) (DialectDenote.exit op args) }

variable [DecidableEq d.Ty] [DialectCall d]

/-- How a path of a run ends, seen at the end of a return: a return of the
values `v` is seen with the traced state `s` it ends in. -/
def TraceState.endOf {V : Type} (μ : Nat → N) (ar : AddrRule) {w : N → Nat} (s : TraceState N w) :
    Except Stuck (Result V) → Except Stuck (Result (End w μ ar V))
  | .ok (.ret v) => .ok (.ret ⟨v, s.mem, s.escaped⟩)
  | .ok .fuelExhausted => .ok .fuelExhausted
  | .error e => .error e

variable (μ : Nat → N) (ar : AddrRule)

/-- The traced runs of the function `f` of the module `M`, where a run names
the dialect's memory `x` as `ρ x`, whose layout entry is `lay (ρ x)`, and
gives each op the items `L`: its run
in the traced layer of marked traces, each op that runs by the dialect's
rule showing a step before it, from the memories that hold `L`'s starting
allocations, with nothing escaped, at each budget, on each argument vector of its parameter types. An
observer sees the acts of the trace and the end of each return, where the
memory numbered `n` is `μ n` and addresses are compared by `ar`. The caller
gives `μ`: it should name the memory numbered `n` as `ρ` names the
dialect's memory of that number, as `μ = ρ` does for the core, whose
memories are their numbers. -/
def Func.traceRuns (M : Module d) (f : Func d) :
    FuncTraceRuns (HVector toType (f.params.map (·.2))) (DialectTrace.Acts d)
      (End (unitsOf lay) μ ar (List (DVal d))) :=
  letI := DialectTrace.stepAt (d := d) lay ρ L
  fun args fuel e => ∃ e',
    (f.run M (m := TraceM (Step (DialectTrace.Acts d)) (TraceState N (unitsOf lay))) args fuel).run
      (TraceState.init (RunItems.start d lay ρ L)) e' ∧ e = e'.map fun p => (p.2.2.endOf μ ar p.1, p.2.1)

/-- The spec's traced runs of the function `f`: its traced runs, where the
end of each return compares no addresses (`AddrRule.ignore`). An address is
seen only through the integers a run shows. The human ruled this on
2026-11-20, on #233. -/
abbrev Func.observedRuns (M : Module d) (f : Func d) :
    FuncTraceRuns (HVector toType (f.params.map (·.2))) (DialectTrace.Acts d)
      (ObservedEnd (unitsOf lay) μ (List (DVal d))) :=
  f.traceRuns lay ρ L μ AddrRule.ignore M

/-- Erasing the steps of the traced runs of a function gives its runs in the
traced layer by the dialect's rules alone. -/
theorem Func.run_eraseSteps (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    letI := DialectTrace.stepAt (d := d) lay ρ L
    letI := DialectTrace.traceAt (d := d) lay ρ L
    ((MonadMorphism.mapActs (TraceState N (unitsOf lay)) Step.acts).except Stuck).map
        (f.run M (m := TraceM (Step (DialectTrace.Acts d)) (TraceState N (unitsOf lay))) args fuel) =
      f.run M (m := TraceM (DialectTrace.Acts d) (TraceState N (unitsOf lay))) args fuel := by
  letI := DialectTrace.stepAt (d := d) lay ρ L
  letI := DialectTrace.traceAt (d := d) lay ρ L
  have hstep : ∀ {α : Type} (x : TraceM (DialectTrace.Acts d) (TraceState N (unitsOf lay)) α),
      TraceM.mapActs Step.acts (TraceM.tick >>= fun _ => TraceM.mapActs (fun a => [.act a]) x) = x := by
    intro α x
    rw [TraceM.mapActs_bind]
    have htick : TraceM.mapActs (σ := TraceState N (unitsOf lay)) (A := Step (DialectTrace.Acts d))
        Step.acts TraceM.tick = pure () := by
      funext s e
      exact propext ⟨fun ⟨_, h, he⟩ => by cases (h : _ = _); exact he, fun h => ⟨_, rfl, h⟩⟩
    rw [htick, TraceM.pure_bind, TraceM.mapActs_mapActs]
    exact TraceM.mapActs_singleton x
  have hmaps : (MonadMorphism.mapActs (TraceState N (unitsOf lay))
      (Step.acts (A := DialectTrace.Acts d))).MapsDenote (d := d) := by
    constructor <;> intro op args
    · exact hstep (DialectDenote.denote (m := TraceM (DialectTrace.Acts d) _) op args)
    · exact hstep (DialectDenote.exit (m := TraceM (DialectTrace.Acts d) _) op args)
  exact Func.run_map hmaps (MonadMorphism.mapActs_mapsFrame _) M f args fuel

/-- A dialect whose ops show no event: wherever a run names its memories,
whatever items it gives each op, its semantics in the traced layer is its
semantics with memory, lifted onto the memories of the traced state. -/
class LiftsMem (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
    [DialectCall d] [DialectEffects d] [DialectMemDenote d] [DialectTrace d] : Prop where
  lifts : ∀ {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N)
      (L : RunItems),
    letI := DialectMemDenote.denoteAt (d := d) lay ρ L
    letI := DialectTrace.traceAt (d := d) lay ρ L
    (MonadMorphism.traceMem N (unitsOf lay) (DialectTrace.Acts d)).MapsDenote (d := d)

/-- The runs with memory of the function `f`, each return seen at its end:
the returned values and the memories it ends with, with nothing escaped.
They start from the memories that hold `L`'s starting allocations, as the
runs with memory do. -/
def Func.memEndRuns [DialectMemDenote d] (M : Module d) (f : Func d) :
    FuncRuns (HVector toType (f.params.map (·.2))) (End (unitsOf lay) μ ar (List (DVal d))) :=
  letI := DialectMemDenote.denoteAt (d := d) lay ρ L
  fun args fuel => Functor.map (f := SetM)
    (fun p => (TraceState.mk p.2 []).endOf μ ar p.1)
    ((f.run M (m := StateT (Memories N (unitsOf lay)) SetM) args fuel).run
      (RunItems.start d lay ρ L))

/-- The traced runs of a function of a dialect whose ops show no event show
no act, and end as its runs with memory, each return seen at its end. -/
theorem Func.traceRuns_noActs [DialectMemDenote d] [LiftsMem d] (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    (f.traceRuns lay ρ L μ ar M args fuel).NoActs (f.memEndRuns lay ρ L μ ar M args fuel) := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ L
  letI := DialectTrace.traceAt (d := d) lay ρ L
  letI := DialectTrace.stepAt (d := d) lay ρ L
  have hY : TraceM.mapActs Step.acts
      ((f.run M (m := TraceM (Step (DialectTrace.Acts d)) (TraceState N (unitsOf lay))) args fuel).run) =
      TraceM.liftMem (f.run M (m := StateT (Memories N (unitsOf lay)) SetM) args fuel).run :=
    (congrArg ExceptT.run (Func.run_eraseSteps lay ρ L M f args fuel)).trans
      (congrArg ExceptT.run (Func.run_map (LiftsMem.lifts lay ρ L)
        MonadMorphism.traceMem_mapsFrame M f args fuel)).symm
  have hfwd : ∀ e', ((f.run M (m := TraceM (Step (DialectTrace.Acts d))
        (TraceState N (unitsOf lay))) args fuel).run (TraceState.init (RunItems.start d lay ρ L)) e') →
      TraceM.liftMem (A := DialectTrace.Acts d)
        (f.run M (m := StateT (Memories N (unitsOf lay)) SetM) args fuel).run (TraceState.init (RunItems.start d lay ρ L))
        (e'.mapActs Step.acts) := fun e' h => hY ▸ ⟨e', h, rfl⟩
  have hbwd : ∀ e, TraceM.liftMem (A := DialectTrace.Acts d)
      (f.run M (m := StateT (Memories N (unitsOf lay)) SetM) args fuel).run (TraceState.init (RunItems.start d lay ρ L)) e →
      ∃ e', ((f.run M (m := TraceM (Step (DialectTrace.Acts d)) (TraceState N (unitsOf lay))) args
        fuel).run (TraceState.init (RunItems.start d lay ρ L)) e') ∧ e = e'.mapActs Step.acts := fun e h => (hY ▸ h :)
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
      obtain ⟨rfl, -, rfl⟩ := he
      exact .inl ⟨_, hz, rfl⟩
    · cases he
  · rintro (⟨⟨_, S'⟩, hz, he⟩ | ⟨_, _, he⟩) <;> cases (he : _ = _)
    obtain ⟨(⟨_, _⟩ | ⟨_, mt, _⟩), h, he⟩ := hbwd _ (.inl ⟨_, S', hz, rfl⟩)
    · cases he
    · simp only [TraceEnd.mapActs, Except.ok.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, -, rfl⟩ := he
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
no event is its observable behaviour with memory, each return seen at its
end, each outcome with an empty trace. -/
theorem Func.traceObservable_traceRuns [DialectMemDenote d] [LiftsMem d] (M : Module d)
    (f : Func d) (args : HVector toType (f.params.map (·.2))) :
    traceObservable (f.traceRuns lay ρ L μ ar M args) =
      .ofBehaviour (observable (f.memEndRuns lay ρ L μ ar M args)) :=
  traceObservable_of_noActs (Func.traceRuns_noActs lay ρ L μ ar M f args)

end Fir
