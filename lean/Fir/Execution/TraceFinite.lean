import Fir.Execution.TraceArgs
import Fir.Execution.TraceSteps

/-!
# Ops of finitely many outcomes, given the world's answers

Divergence of traced runs needs one trace of the source that serves every
budget. The human ruled on 2026-11-20, on #233, that the traced layer's
theorems take a hypothesis for it: each op has finitely many outcomes, given
the world's answers. The core's and CoreGpu's statements take no such
hypothesis; they meet it.

_Given the world's answers_ means by position. An _answer stream_ says, for
each place of a trace, the answer that the world gives there, or that the
trace has no act there. A trace _agrees_ with the stream when the answer of
each of its acts is the stream's at its place. An op has finitely many
outcomes, given the world's answers, when, from each traced state and for
each answer stream, the outcomes that it may end with and whose acts agree
with the stream, each a result with its acts and the traced state, are among
those of a list. UB is not counted: a path that hits UB ends there.

The stream fixes the answers by position, not a list of them. An op that may
show _k_ events for every _k_ has, for each list of answers, finitely many
outcomes whose answers start that list, one for each _k_ up to its length;
but against a stream of answers that goes on forever it has infinitely many,
so it does not meet the hypothesis (`FirTest.TraceDiverge`). The argument
for this form, that with such an op a target could show acts forever that
no single run of the source shows, is on paper; it is not checked in Lean.
The human ruled the hypothesis; its form by position is this module's,
recorded on `docs/decisions/semantics-m1-trace.md`. The toy `emit` of
`FirTest.TraceDialect`, which shows one event and takes any answer, meets
it: the stream fixes the answer.

Two ways of building an op's semantics keep the hypothesis:

* _The step before an op._ In the traced layer of marked traces, an op runs
  by its dialect's rule after a step (`DialectTrace.stepAt`): its outcomes
  are its rule's, each after a step, and agree with a stream as its rule's
  acts do. Every path of such an op shows exactly one step.
* _The lift of the semantics with memory._ A dialect whose ops show no event
  runs each op by its rule with memory, on the memories of the traced state
  (`DialectTrace.ofMem`). An op with finitely many outcomes with memory
  (`OpsFinite`) has finitely many in the traced layer: the lift shows
  nothing and keeps what escaped.
-/

namespace Fir

open Memory

variable {E Ans σ α : Type}

/-! # Answers by position -/

/-- The trace `t` agrees with the answer stream `ans`: the answer of each of its
acts is the stream's answer at its place. -/
def Act.Agrees (ans : Nat → Option Ans) (t : List (Act E Ans)) : Prop :=
  ∀ i a, t[i]? = some a → ans i = some a.answer

/-- A trace that starts one that agrees with a stream agrees with it. -/
theorem Act.Agrees.of_prefix {ans : Nat → Option Ans} {t t' : List (Act E Ans)}
    (h : Act.Agrees ans t') (hp : t <+: t') : Act.Agrees ans t :=
  fun i a ha => h i a (List.IsPrefix.getElem?_some hp ha)

/-- Two traces, one after the other, agree with a stream when the first does
and the second agrees with the rest of the stream, after the first's
places. -/
theorem Act.agrees_append {ans : Nat → Option Ans} {t t' : List (Act E Ans)} :
    Act.Agrees ans (t ++ t') ↔ Act.Agrees ans t ∧ Act.Agrees (fun i => ans (t.length + i)) t' := by
  constructor
  · intro h
    refine ⟨fun i a ha => h i a ?_, fun i a ha => h (t.length + i) a ?_⟩
    · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 ha).1]
      exact ha
    · rw [List.getElem?_append_right (by omega)]
      simpa using ha
  · rintro ⟨h, h'⟩ i a ha
    by_cases hi : i < t.length
    · rw [List.getElem?_append_left hi] at ha
      exact h i a ha
    · rw [List.getElem?_append_right (by omega)] at ha
      have := h' (i - t.length) a ha
      dsimp only at this
      rwa [Nat.add_sub_cancel' (by omega)] at this

variable [HRefinement E E]

/-- A trace refined by a prefix of one that agrees with a stream agrees with
it: refinement of acts keeps their answers. -/
theorem Act.Agrees.of_isRefinedPrefix {ans : Nat → Option Ans} {t t' : List (Act E Ans)}
    (h : Act.Agrees ans t') (hp : List.IsRefinedPrefix t t') : Act.Agrees ans t := fun i a ha => by
  obtain ⟨b, hb, hab⟩ := List.IsRefinedPrefix.getElem? hp i a ha
  rw [h i b hb, hab.2]

/-! # Finitely many outcomes -/

/-- A computation of the traced layer has finitely many outcomes, given the
world's answers: from each traced state and for each answer stream, each
result it may end with, with acts that agree with the stream and the traced
state, is in a list. -/
def TraceFinitelyMany (c : TraceM (Act E Ans) σ α) : Prop :=
  ∀ s (ans : Nat → Option Ans), ∃ L : List (α × List (Act E Ans) × σ),
    ∀ a t s', c s (.ok (a, t, s')) → Act.Agrees ans t → (a, t, s') ∈ L

/-- A computation of the traced layer of marked traces has finitely many
outcomes, given the world's answers: as for the traced layer, with the acts
of each marked trace agreeing with the stream. -/
def StepFinitelyMany (c : TraceM (Step (Act E Ans)) σ α) : Prop :=
  ∀ s (ans : Nat → Option Ans), ∃ L : List (α × List (Step (Act E Ans)) × σ),
    ∀ a mt s', c s (.ok (a, mt, s')) → Act.Agrees ans (Step.actsOf mt) → (a, mt, s') ∈ L

/-- The acts of a trace, each mapped to the act of a marked trace, are the
trace. -/
theorem Step.actsOf_flatMap_act {A : Type} (t : List A) :
    Step.actsOf (t.flatMap fun a => [Step.act a]) = t := by
  induction t with
  | nil => rfl
  | cons a t ih => simpa [Step.actsOf, Step.acts] using ih

omit [HRefinement E E] in
/-- A computation with finitely many outcomes, given the world's answers,
still has after a step, each act of its traces an act of the marked trace. -/
theorem TraceFinitelyMany.step {c : TraceM (Act E Ans) σ α} (h : TraceFinitelyMany c) :
    StepFinitelyMany (TraceM.tick >>= fun _ => TraceM.mapActs (fun a => [Step.act a]) c) := by
  intro s ans
  obtain ⟨L, hL⟩ := h s ans
  refine ⟨L.map fun p => (p.1, .tick :: p.2.1.flatMap (fun a => [Step.act a]), p.2.2),
    fun a mt s' hc hag => ?_⟩
  rcases (TraceM.bind_apply _ _ _ _).1 hc with ⟨_, t, s₁, e₁, ht, ⟨e₀, hc₀, rfl⟩, he⟩ | ⟨_, _, ht, _⟩
  · have ht : (Except.ok ((), t, s₁) : TraceEnd (Step (Act E Ans)) σ Unit) = .ok ((), [.tick], s) := ht
    cases ht
    rcases e₀ with ⟨_, _⟩ | ⟨a₀, t₀, s₀⟩
    · cases he
    · simp only [TraceEnd.mapActs, TraceEnd.after, Except.ok.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have hag₀ : Act.Agrees ans t₀ := by
        have e : Step.actsOf ([Step.tick] ++ t₀.flatMap fun a => [Step.act a]) = t₀ :=
          Step.actsOf_flatMap_act t₀
        rwa [e] at hag
      exact List.mem_map.2 ⟨_, hL _ _ _ hc₀ hag₀, rfl⟩
  · cases ht

omit [HRefinement E E] in
/-- An op's computation, mapped by the lift of the semantics with memory,
has finitely many outcomes, given the world's answers, when it has finitely
many with memory: the lift shows nothing and keeps what escaped. -/
theorem FinitelyMany.liftMem {Mem : Type} {unit : Mem → Nat}
    {c : StateT (Memories Mem unit) SetM α} (h : FinitelyMany c) :
    TraceFinitelyMany (E := E) (Ans := Ans) (TraceM.liftMem c : TraceM _ (TraceState Mem unit) α) := by
  intro s _
  obtain ⟨L, hL⟩ := h s.mem
  refine ⟨L.map fun p => (p.1, [], { s with mem := p.2 }), fun a t s' hc _ => ?_⟩
  rcases hc with ⟨a', S', hc, he⟩ | ⟨_, _, he⟩
  · cases he
    exact List.mem_map.2 ⟨(a, S'), hL _ hc, rfl⟩
  · cases he

/-! # Ops of finitely many outcomes -/

/-- Every op of `d` that runs by its own rule, a terminator or an op with no
callee, has finitely many outcomes in the traced layer, given the world's
answers, from each operands, as an op that is not a terminator and as a
terminator. -/
def OpsTraceFinite (d : Dialect) [TyDenote d.Ty] [DialectSignature d] [DialectCall d]
    (E Ans σ : Type) [DialectDenote d (TraceM (Act E Ans) σ)] : Prop :=
  ∀ op : d.Op, isTerminator op = true ∨ callee? op = none → ∀ args : HVector toType (sig op),
    (isTerminator op = false →
      TraceFinitelyMany (DialectDenote.denote (m := TraceM (Act E Ans) σ) op args)) ∧
    (isTerminator op = true →
      TraceFinitelyMany (DialectDenote.exit (m := TraceM (Act E Ans) σ) op args))

/-- Every op of `d` that runs by its own rule has finitely many outcomes in
the traced layer of marked traces, given the world's answers. -/
def OpsStepFinite (d : Dialect) [TyDenote d.Ty] [DialectSignature d] [DialectCall d]
    (E Ans σ : Type) [DialectDenote d (TraceM (Step (Act E Ans)) σ)] : Prop :=
  ∀ op : d.Op, isTerminator op = true ∨ callee? op = none → ∀ args : HVector toType (sig op),
    (isTerminator op = false →
      StepFinitelyMany (DialectDenote.denote (m := TraceM (Step (Act E Ans)) σ) op args)) ∧
    (isTerminator op = true →
      StepFinitelyMany (DialectDenote.exit (m := TraceM (Step (Act E Ans)) σ) op args))

/-- Every path of every op of `d` shows exactly one step, from every traced
state, as an op that is not a terminator and as a terminator. -/
def OpsOneStep (d : Dialect) [TyDenote d.Ty] [DialectSignature d] (A σ : Type)
    [DialectDenote d (TraceM (Step A) σ)] : Prop :=
  ∀ (op : d.Op) (args : HVector toType (sig op)) (s : σ),
    (∀ e, DialectDenote.denote (m := TraceM (Step A) σ) op args s e → Step.ticks e.trace = 1) ∧
    (∀ e, DialectDenote.exit (m := TraceM (Step A) σ) op args s e → Step.ticks e.trace = 1)

/-- After a step, each act of its traces an act of the marked trace, every
path of a computation shows exactly one step. -/
theorem TraceM.step_ticks {A : Type} {c : TraceM A σ α} {s : σ} {e : TraceEnd (Step A) σ α}
    (h : (TraceM.tick >>= fun _ => TraceM.mapActs (fun a => [Step.act a]) c) s e) :
    Step.ticks e.trace = 1 := by
  rcases (TraceM.bind_apply _ _ _ _).1 h with ⟨_, t, s₁, e₁, ht, ⟨e₀, -, rfl⟩, rfl⟩ | ⟨_, _, ht, _⟩
  · have ht : (Except.ok ((), t, s₁) : TraceEnd (Step A) σ Unit) = .ok ((), [.tick], s) := ht
    cases ht
    have h0 : ∀ l : List A, Step.ticks (l.flatMap fun a => [Step.act a]) = 0 := by
      intro l
      induction l with
      | nil => rfl
      | cons a l ih => simpa [Step.ticks] using ih
    rw [TraceEnd.trace_after, TraceEnd.trace_mapActs]
    simp [Step.ticks, h0]
  · cases ht

section

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectEffects d]
  {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (L : RunItems)

/-- In the traced layer of marked traces, every path of every op shows
exactly one step, the one before the op. -/
theorem DialectTrace.stepAt_oneStep [DialectTrace d] :
    letI := DialectTrace.stepAt (d := d) lay ρ L
    OpsOneStep d (DialectTrace.Acts d) (TraceState N (unitsOf lay)) :=
  fun _ _ _ => ⟨fun _ h => TraceM.step_ticks h, fun _ h => TraceM.step_ticks h⟩

variable [DialectCall d]

/-- Ops of finitely many outcomes in the traced layer, given the world's
answers, have finitely many in the traced layer of marked traces, where each
runs after a step. -/
theorem OpsTraceFinite.stepAt [DialectTrace d]
    (h : letI := DialectTrace.traceAt (d := d) lay ρ L
      OpsTraceFinite d (DialectTrace.Event d) (DialectTrace.Answer d) (TraceState N (unitsOf lay))) :
    letI := DialectTrace.stepAt (d := d) lay ρ L
    OpsStepFinite d (DialectTrace.Event d) (DialectTrace.Answer d) (TraceState N (unitsOf lay)) :=
  fun op hop args => ⟨fun hT => ((h op hop args).1 hT).step, fun hT => ((h op hop args).2 hT).step⟩

/-- In the traced semantics of a dialect whose ops show no event, ops of
finitely many outcomes with memory have finitely many in the traced layer,
given the world's answers. -/
theorem OpsTraceFinite.ofMem [DialectMemDenote d]
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ L
      OpsFinite d N (unitsOf lay)) :
    letI := DialectTrace.ofMem d
    letI := DialectTrace.traceAt (d := d) lay ρ L
    OpsTraceFinite d (DialectTrace.Event d) (DialectTrace.Answer d) (TraceState N (unitsOf lay)) :=
  fun op hop args => ⟨fun hT => FinitelyMany.liftMem ((h op hop args).1 hT),
    fun hT => FinitelyMany.liftMem ((h op hop args).2 hT)⟩

end

end Fir
