import Fir.Execution.TraceMonad
import Fir.Execution.MemoryRuns

/-!
# Traced runs

A traced run at one budget is the set of the ways it may end, each with the
trace it showed: with a result, or stuck, or with UB and its reason. Its
traced observable behaviour is what it shows over every budget:

* a return or UB, after a finite trace, that some budget reaches;
* silent divergence after the finite trace _t_: at every budget the run can
  run out of fuel having shown a prefix of _t_, and from some budget on
  having shown _t_ itself;
* an infinite trace: for each _k_, from some budget on, the run can run out
  of fuel having shown the first _k_ acts of the trace.

As for M0's outcomes, reading divergence so assumes that every choice has
finitely many options. Then, by König's lemma, a run that can run out of
fuel at every budget having shown more and more of a trace has one infinite
path along which it shows that trace (the section on outcomes and
behaviours).

A run with no event is a traced run whose every path shows an empty trace.
Its traced observable behaviour is its observable behaviour, each outcome
with an empty trace, divergence silent from the start; and refinement of
such traced behaviours is refinement of the behaviours.

# A dialect's events

A dialect says what its events and their answers are, how one event refines
another, and gives its ops a semantics in the traced layer, wherever a run
names its memories. The traced runs of a function are the runs of the
interpreter in that layer, from no trace and the empty memories. A dialect
whose ops show no event has, in the traced layer, its semantics with memory,
lifted: its traced runs are then its runs with memory with an empty trace,
and every theorem about the refinement of its runs with memory holds of its
traced runs. M0's tests have no events, so they keep their results.
-/

namespace Fir

open Memory

/-! # Traced runs and their behaviour -/

/-- A traced run at one budget: the set of the ways it may end, each with the
trace it showed. A path ends with a result or stuck, after the trace, or
with UB, its reason and the trace. -/
abbrev TRun (A O : Type) : Type :=
  Paths (Except (String × List A) (Except Stuck (Result O) × List A))

variable {A O : Type}

/-- The traced observable behaviour of a run that takes fuel: each return and
UB that some budget reaches, with its trace; silent divergence after a
finite trace; and the infinite traces that the run shows more and more of
as its budget grows. -/
def traceObservable (run : Nat → TRun A O) : TBehaviour A O
  | .ret tr o => ∃ n, run n (.ok (.ok (.ret o), tr))
  | .ub tr r => ∃ n, run n (.error (r, tr))
  | .diverge tr => ∃ N, ∀ n, ∃ tr', run n (.ok (.ok .fuelExhausted, tr')) ∧ tr' <+: tr ∧
      (N ≤ n → tr' = tr)
  | .reacts T => ∀ k, ∃ N, ∀ n, N ≤ n →
      ∃ tr, run n (.ok (.ok .fuelExhausted, tr)) ∧ ∀ i, i < k → tr[i]? = some (T i)

/-- A run with no event, as a traced run whose every path shows an empty
trace. -/
def TRun.ofRun (s : Run O) : TRun A O
  | .ok (r, tr) => tr = [] ∧ s (.ok r)
  | .error (r, tr) => tr = [] ∧ s (.ub r)

/-- The traced observable behaviour of a run with no event is its observable
behaviour, each outcome with an empty trace. -/
theorem traceObservable_ofRun (run : Nat → Run O) :
    traceObservable (A := A) (fun n => TRun.ofRun (run n)) = .ofBehaviour (observable run) := by
  funext t
  apply propext
  cases t with
  | ret tr o =>
    constructor
    · rintro ⟨n, rfl, h⟩
      exact ⟨.ret o, ⟨n, h⟩, rfl⟩
    · rintro ⟨o' | _ | _, h, he⟩ <;> cases he
      obtain ⟨n, h⟩ := h
      exact ⟨n, rfl, h⟩
  | ub tr r =>
    constructor
    · rintro ⟨n, rfl, h⟩
      exact ⟨.ub r, ⟨n, h⟩, rfl⟩
    · rintro ⟨_ | r' | _, h, he⟩ <;> cases he
      obtain ⟨n, h⟩ := h
      exact ⟨n, rfl, h⟩
  | diverge tr =>
    constructor
    · rintro ⟨N, h⟩
      obtain ⟨_, ⟨rfl, _⟩, _, hN⟩ := h N
      cases hN (Nat.le_refl N)
      exact ⟨.fuelExhausted, fun n => (h n).elim fun _ h => h.1.2, rfl⟩
    · rintro ⟨_ | _ | _, h, he⟩ <;> cases he
      exact ⟨0, fun n => ⟨[], ⟨rfl, h n⟩, List.prefix_refl [], fun _ => rfl⟩⟩
  | reacts T =>
    constructor
    · intro h
      obtain ⟨N, hN⟩ := h 1
      obtain ⟨_, ⟨rfl, _⟩, h0⟩ := hN N (Nat.le_refl N)
      exact nomatch h0 0 Nat.one_pos
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

/-- The runs of a function with no event, as traced runs. -/
def ofFuncRuns (F : FuncRuns Args O) : FuncTraceRuns Args A O :=
  fun a n => TRun.ofRun (F a n)

/-- Functions with no event refine as traced functions exactly when they
refine as functions. -/
theorem ofFuncRuns_isRefinedBy_iff {src tgt : FuncRuns Args O} :
    (ofFuncRuns src : FuncTraceRuns Args A O) ⊑ (ofFuncRuns tgt : FuncTraceRuns Args A O) ↔
      src ⊑ tgt := by
  show (∀ a, _) ↔ ∀ a, _
  refine forall_congr' fun a => ?_
  show traceObservable (fun n => TRun.ofRun (src a n)) ⊑
      traceObservable (fun n => TRun.ofRun (tgt a n)) ↔ _
  rw [traceObservable_ofRun, traceObservable_ofRun]
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

variable [DecidableEq d.Ty] [DialectCall d] {N : Type} [DecidableEq N] (lay : N → MemLayout)
  (ρ : DialectEffects.Mem d → N)

/-- The traced runs of the function `f` of the module `M`, where a run names
the dialect's memory `x` as `ρ x`, whose layout entry is `lay (ρ x)`: its run
in the traced layer, by the dialect's semantics there, from no trace and the
empty memories, at each budget, on each argument vector of its parameter
types. An observer sees the trace and what it returns. -/
def Func.traceRuns (M : Module d) (f : Func d) :
    FuncTraceRuns (HVector toType (f.params.map (·.2))) (DialectTrace.Acts d) (List (DVal d)) :=
  letI := DialectTrace.traceAt (d := d) lay ρ
  fun args fuel e => ∃ e',
    (f.run M (m := TraceM (DialectTrace.Acts d) (Memories N (unitsOf lay))) args fuel).run
      ([], Memories.empty) e' ∧ e = e'.map fun p => (p.1, p.2.1)

/-- A dialect whose ops show no event: wherever a run names its memories,
its semantics in the traced layer is its semantics with memory, lifted. -/
class LiftsMem (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
    [DialectCall d] [DialectEffects d] [DialectMemDenote d] [DialectTrace d] : Prop where
  lifts : ∀ {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N),
    letI := DialectMemDenote.denoteAt (d := d) lay ρ
    letI := DialectTrace.traceAt (d := d) lay ρ
    (MonadMorphism.trace (DialectTrace.Acts d) (Memories N (unitsOf lay))).MapsDenote (d := d)

/-- The traced runs of a function of a dialect whose ops show no event are its
runs with memory, each path with an empty trace. -/
theorem Func.traceRuns_eq [DialectMemDenote d] [LiftsMem d] (M : Module d) (f : Func d) :
    f.traceRuns lay ρ M = .ofFuncRuns (f.memRuns lay ρ M) := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ
  letI := DialectTrace.traceAt (d := d) lay ρ
  funext args fuel e
  have hrun := Func.run_map (LiftsMem.lifts lay ρ) MonadMorphism.trace_mapsFrame M f args fuel
  simp only [Func.traceRuns, ← hrun, MonadMorphism.except, MonadMorphism.trace, ExceptT.run,
    ExceptT.mk, TraceM.lift, FuncTraceRuns.ofFuncRuns, Func.memRuns]
  apply propext
  rcases e with ⟨r, tr⟩ | ⟨a, tr⟩ <;>
    simp only [TRun.ofRun, Functor.map, Function.comp] <;> constructor
  · rintro ⟨_, (⟨_, _, _, rfl⟩ | ⟨r', h, rfl⟩), he⟩ <;> cases he
    exact ⟨rfl, .inr ⟨r, h, rfl⟩⟩
  · rintro ⟨rfl, (⟨_, _, he⟩ | ⟨r', h, he⟩)⟩ <;> cases he
    exact ⟨_, .inr ⟨r, h, rfl⟩, rfl⟩
  · rintro ⟨_, (⟨a, s', h, rfl⟩ | ⟨_, _, rfl⟩), he⟩ <;> cases he
    exact ⟨rfl, .inl ⟨(a, s'), h, rfl⟩⟩
  · rintro ⟨rfl, (⟨⟨a, s'⟩, h, he⟩ | ⟨_, _, he⟩)⟩ <;> cases he
    exact ⟨_, .inl ⟨a, s', h, rfl⟩, rfl⟩

end Fir
