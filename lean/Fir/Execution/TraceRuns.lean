import Fir.Execution.TraceMonad
import Fir.Execution.MemoryRuns

/-!
# Traced runs

A traced run marks its steps. Before each op runs by its rule, the run shows
a _step_, a mark in its trace that the world never sees. So the trace of a
path tells, of each act, how many ops had run when the path showed it. A
traced run at one budget is the set of the ways it may end, each with its
marked trace: with a result, or stuck, or with UB and its reason.

Its traced observable behaviour is what it shows over every budget. The
acts of a marked trace are its trace; the steps only date them.

* A return or UB, after a finite trace, that some budget reaches.
* Silent divergence after the finite trace _t_: from some number _N_ of
  steps on, at every budget the run can run out of fuel having shown _t_,
  all of it in its first _N_ steps; and at every budget it can run out of
  fuel having shown a prefix of _t_.
* An infinite trace _T_: there are numbers of steps _K(k)_ such that at
  every budget _n_ the run can run out of fuel having shown a prefix of _T_,
  with at least _k_ acts in its first _K(k)_ steps whenever _K(k) ≤ n_.

Without the steps, a run that can return arbitrarily late after its last
act could not be told apart from one that falls silent after it, nor a run
that can show arbitrarily many acts before it returns from one that shows
acts forever: at each budget both can run out of fuel after the same acts.
The steps tell them apart. When every choice has finitely many options, the
paths that meet one of these conditions at every budget are the prefixes of
an infinite path, by König's lemma, and that path shows _t_ and then falls
silent, or shows _T_. An event may have infinitely many answers, so an
event's answers count as a choice here too.

A run with no act, whose paths end as a run of the set monad, has the
observable behaviour of that run, each outcome with an empty trace, and
divergence silent from the start; so refinement of such traced runs is
refinement of the runs.

# A dialect's events

A dialect says what its events and their answers are, how one event refines
another, and gives its ops a semantics in the traced layer, wherever a run
names its memories. The traced runs of a function are the runs of the
interpreter in the traced layer of marked traces, where each op shows a
step and then runs by the dialect's rule, from the empty memories. Erasing
the steps maps them to the runs by the dialect's rules alone. A dialect
whose ops show no event has, in the traced layer, its semantics with memory,
lifted: its traced runs then show no act and end as its runs with memory,
and every theorem about the refinement of its runs with memory holds of its
traced runs. M0's tests have no events, so they keep their results.
-/

namespace Fir

open Memory

/-! # Marked traces -/

/-- An element of a marked trace: a step of the run, or an act. -/
inductive Step (A : Type) where
  | tick
  | act (a : A)

variable {A O : Type}

/-- The acts of an element of a marked trace: none for a step. -/
def Step.acts : Step A → List A
  | .tick => []
  | .act a => [a]

/-- The acts of a marked trace: its trace. -/
def Step.actsOf (mt : List (Step A)) : List A := mt.flatMap Step.acts

/-- What a marked trace shows in its first `N` steps: its elements before its
step `N + 1`. -/
def Step.upTo : Nat → List (Step A) → List (Step A)
  | _, [] => []
  | N, .act a :: mt => .act a :: upTo N mt
  | 0, .tick :: _ => []
  | N + 1, .tick :: mt => .tick :: upTo N mt

/-- What a marked trace shows in its first steps is a prefix of what it
shows. -/
theorem Step.actsOf_upTo_prefix : ∀ (N : Nat) (mt : List (Step A)),
    Step.actsOf (Step.upTo N mt) <+: Step.actsOf mt
  | _, [] => List.prefix_refl []
  | N, .act a :: mt => by
    simpa [upTo, actsOf, acts] using actsOf_upTo_prefix N mt
  | 0, .tick :: mt => by simp [upTo, actsOf]
  | N + 1, .tick :: mt => by
    simpa [upTo, actsOf, acts] using actsOf_upTo_prefix N mt

/-- A marked trace with no act shows none in its first steps. -/
theorem Step.actsOf_upTo_eq_nil {mt : List (Step A)} (h : Step.actsOf mt = []) (N : Nat) :
    Step.actsOf (Step.upTo N mt) = [] := by
  obtain ⟨t, ht⟩ := Step.actsOf_upTo_prefix N mt
  rw [h] at ht
  exact (List.append_eq_nil_iff.mp ht).1

/-! # Traced runs and their behaviour -/

/-- A traced run at one budget: the set of the ways it may end, each with its
marked trace. A path ends with a result or stuck, or with UB and its
reason. -/
abbrev TRun (A O : Type) : Type :=
  Paths (Except (String × List (Step A)) (Except Stuck (Result O) × List (Step A)))

/-- The traced observable behaviour of a run that takes fuel: each return and
UB that some budget reaches, with its trace; silent divergence after a
finite trace that the run shows within a bounded number of steps; and each
infinite trace that the run shows more of in a bounded number of steps as
its budget grows. -/
def traceObservable (run : Nat → TRun A O) : TBehaviour A O
  | .ret tr o => ∃ n mt, run n (.ok (.ok (.ret o), mt)) ∧ Step.actsOf mt = tr
  | .ub tr r => ∃ n mt, run n (.error (r, mt)) ∧ Step.actsOf mt = tr
  | .diverge tr => ∃ N, ∀ n, ∃ mt, run n (.ok (.ok .fuelExhausted, mt)) ∧
      Step.actsOf mt <+: tr ∧ (N ≤ n → Step.actsOf (Step.upTo N mt) = tr)
  | .reacts T => ∃ K : Nat → Nat, ∀ n, ∃ mt, run n (.ok (.ok .fuelExhausted, mt)) ∧
      (∀ i a, (Step.actsOf mt)[i]? = some a → a = T i) ∧
      ∀ k, K k ≤ n → k ≤ (Step.actsOf (Step.upTo (K k) mt)).length

/-- The traced run `R` shows no act, and its paths end as those of the run
`s` of the set monad. -/
structure TRun.NoActs (R : TRun A O) (s : Run O) : Prop where
  ok_acts : ∀ x mt, R (.ok (x, mt)) → Step.actsOf mt = []
  error_acts : ∀ r mt, R (.error (r, mt)) → Step.actsOf mt = []
  ok_iff : ∀ x, (∃ mt, R (.ok (x, mt))) ↔ s (.ok x)
  error_iff : ∀ r, (∃ mt, R (.error (r, mt))) ↔ s (.ub r)

/-- The traced observable behaviour of a run that shows no act is the
observable behaviour of the run of the set monad whose paths it ends as,
each outcome with an empty trace. -/
theorem traceObservable_of_noActs {run : Nat → TRun A O} {s : Nat → Run O}
    (h : ∀ n, (run n).NoActs (s n)) : traceObservable run = .ofBehaviour (observable s) := by
  funext t
  apply propext
  cases t with
  | ret tr o =>
    constructor
    · rintro ⟨n, mt, hr, rfl⟩
      rw [(h n).ok_acts _ _ hr]
      exact ⟨.ret o, ⟨n, (h n).ok_iff _ |>.1 ⟨mt, hr⟩⟩, rfl⟩
    · rintro ⟨o' | _ | _, ho, he⟩ <;> cases he
      obtain ⟨n, hs⟩ := ho
      obtain ⟨mt, hr⟩ := (h n).ok_iff _ |>.2 hs
      exact ⟨n, mt, hr, (h n).ok_acts _ _ hr⟩
  | ub tr r =>
    constructor
    · rintro ⟨n, mt, hr, rfl⟩
      rw [(h n).error_acts _ _ hr]
      exact ⟨.ub r, ⟨n, (h n).error_iff _ |>.1 ⟨mt, hr⟩⟩, rfl⟩
    · rintro ⟨_ | r' | _, ho, he⟩ <;> cases he
      obtain ⟨n, hs⟩ := ho
      obtain ⟨mt, hr⟩ := (h n).error_iff _ |>.2 hs
      exact ⟨n, mt, hr, (h n).error_acts _ _ hr⟩
  | diverge tr =>
    constructor
    · rintro ⟨N, hN⟩
      obtain ⟨mt, hr, _, he⟩ := hN N
      have h0 := Step.actsOf_upTo_eq_nil ((h N).ok_acts _ _ hr) N
      rw [he (Nat.le_refl N)] at h0
      subst h0
      exact ⟨.fuelExhausted, fun n => (h n).ok_iff _ |>.1 ((hN n).elim fun mt h => ⟨mt, h.1⟩), rfl⟩
    · rintro ⟨_ | _ | _, ho, he⟩ <;> cases he
      refine ⟨0, fun n => ?_⟩
      obtain ⟨mt, hr⟩ := (h n).ok_iff _ |>.2 (ho n)
      have h0 := (h n).ok_acts _ _ hr
      exact ⟨mt, hr, h0 ▸ List.prefix_refl [], fun _ => Step.actsOf_upTo_eq_nil h0 0⟩
  | reacts T =>
    constructor
    · rintro ⟨K, hK⟩
      obtain ⟨mt, hr, _, hk⟩ := hK (K 1)
      have h0 := Step.actsOf_upTo_eq_nil ((h _).ok_acts _ _ hr) (K 1)
      have := hk 1 (Nat.le_refl _)
      rw [h0] at this
      simp at this
    · rintro ⟨_ | _ | _, _, he⟩ <;> cases he

/-! # The traced runs of functions -/

/-- The traced runs of a function: for each argument vector, its traced run
at each budget. -/
def FuncTraceRuns (Args A O : Type) : Type := Args → Nat → TRun A O

namespace FuncTraceRuns

variable {Args : Type} [HRefinement A A] [HRefinement O O]

/-- The target function refines the source function: on every argument
vector, its traced observable behaviour refines the source's. -/
def IsRefinedBy (src tgt : FuncTraceRuns Args A O) : Prop :=
  ∀ a, traceObservable (src a) ⊑ traceObservable (tgt a)

instance : HRefinement (FuncTraceRuns Args A O) (FuncTraceRuns Args A O) := ⟨IsRefinedBy⟩

/-- Refinement of traced functions is reflexive when refinement of acts and
of observations is. -/
theorem isRefinedBy_refl (hA : ∀ a : A, a ⊑ a) (hO : ∀ o : O, o ⊑ o)
    (f : FuncTraceRuns Args A O) : f ⊑ f :=
  fun a => TBehaviour.isRefinedBy_refl hA hO (traceObservable (f a))

/-- Refinement of traced functions is transitive when refinement of acts and
of observations is. -/
theorem isRefinedBy_trans (hA : ∀ {a b c : A}, a ⊑ b → b ⊑ c → a ⊑ c)
    (hO : ∀ {a b c : O}, a ⊑ b → b ⊑ c → a ⊑ c) {f g h : FuncTraceRuns Args A O}
    (hfg : f ⊑ g) (hgh : g ⊑ h) : f ⊑ h :=
  fun a => TBehaviour.isRefinedBy_trans hA hO (hfg a) (hgh a)

/-- Traced functions that show no act refine exactly when the functions whose
runs they end as refine. -/
theorem isRefinedBy_iff_of_noActs {src tgt : FuncTraceRuns Args A O} {F G : FuncRuns Args O}
    (hs : ∀ a n, (src a n).NoActs (F a n)) (ht : ∀ a n, (tgt a n).NoActs (G a n)) :
    src ⊑ tgt ↔ F ⊑ G := by
  show (∀ a, _) ↔ ∀ a, _
  refine forall_congr' fun a => ?_
  rw [traceObservable_of_noActs (hs a), traceObservable_of_noActs (ht a)]
  exact TBehaviour.ofBehaviour_isRefinedBy_iff

end FuncTraceRuns

/-- Refinement of traced functions holds for every world: on every argument
vector, at every world, each outcome that the target shows there is allowed
by an outcome of the source, which shows the same answers. -/
theorem FuncTraceRuns.isRefinedBy_iff_world {Args E Ans : Type} [HRefinement E E]
    [HRefinement O O] [Inhabited Ans] {src tgt : FuncTraceRuns Args (Act E Ans) O} :
    src ⊑ tgt ↔ ∀ a w t, (traceObservable (tgt a)).atWorld w t →
      ∃ s, traceObservable (src a) s ∧ s ⊑ t :=
  forall_congr' fun _ => TBehaviour.isRefinedBy_iff_world

/-! # A dialect's events -/

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
in the traced layer of marked traces, each op showing a step before it runs
by the dialect's rule, from the empty memories, at each budget, on each
argument vector of its parameter types. An observer sees the acts of the
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
