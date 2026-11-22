import Fir.Execution.TraceFinite
import Fir.Execution.TraceStepPaths

/-!
# Finitely many traces at one budget

When every op that runs by its own rule, and every external call, has
finitely many outcomes, given the world's answers
(`Fir.Execution.TraceFinite`), a traced run of ops at
one budget has finitely many outcomes, given the world's answers, calls and
recursion included: from each traced state and for each answer stream, the
results it may end with, with marked traces whose acts agree with the
stream and the traced states, are among those of a list.

The interpreter's building blocks keep finitely many outcomes:

* `pure` and a check end in one way, showing nothing;
* an op's rule, and the external-call rule, has finitely many by the
  hypothesis;
* a sequence goes on, from each of its first computation's finitely many
  outcomes, in finitely many ways, given the rest of the stream after the
  first's acts; so it has finitely many;
* a run in a call's frame has its ops' outcomes, its frame left.

The proof that a run of ops has finitely many is by strong induction on the
budget, following the interpreter's definition: a callee runs at a smaller
budget, and so does the rest of the run after each op.
-/

namespace Fir

open Memory

variable {E Ans σ α β : Type}

/-! # The interpreter's computations -/

/-- A computation of the interpreter in the traced layer of marked traces
has finitely many outcomes, given the world's answers: from each state and
for each answer stream, each value it may end with, with a marked trace
whose acts agree with the stream and the state, is in a list. -/
def ExceptStepFinite (x : ExceptT Stuck (TraceM (Step (Act E Ans)) σ) α) : Prop :=
  ∀ s (ans : Nat → Option Ans), ∃ L : List (α × List (Step (Act E Ans)) × σ),
    ∀ a mt s', x.run s (.ok (.ok a, mt, s')) → Act.Agrees ans (Step.actsOf mt) → (a, mt, s') ∈ L

namespace ExceptStepFinite

/-- `pure` ends in one way. -/
theorem pure (a : α) : ExceptStepFinite (Pure.pure a : ExceptT Stuck (TraceM (Step (Act E Ans)) σ) α) :=
  fun s _ => ⟨[(a, [], s)], fun _ _ _ h _ => by
    cases (TraceM.run_except_pure _ _ _).1 h
    exact List.mem_singleton_self _⟩

/-- A check ends in one way. -/
theorem liftExcept (x : Except Stuck α) :
    ExceptStepFinite (liftExcept x : ExceptT Stuck (TraceM (Step (Act E Ans)) σ) α) :=
  fun s _ => ⟨match x with | .ok a => [(a, [], s)] | .error _ => [], fun _ _ _ h _ => by
    have h := (TraceM.run_liftExcept _ _ _).1 h
    cases x with
    | ok a =>
      cases h
      exact List.mem_singleton_self _
    | error _ => cases h⟩

/-- A computation of the traced layer with finitely many outcomes, run by
the interpreter. -/
theorem lift {c : TraceM (Step (Act E Ans)) σ α} (h : StepFinitelyMany c) :
    ExceptStepFinite (ExceptT.lift c : ExceptT Stuck (TraceM (Step (Act E Ans)) σ) α) :=
  fun s ans => by
    obtain ⟨L, hL⟩ := h s ans
    refine ⟨L, fun a mt s' hx hag => ?_⟩
    rcases (TraceM.run_lift _ _ _).1 hx with ⟨_, _, _, hc, he⟩ | ⟨_, _, _, he⟩ <;> cases he
    exact hL _ _ _ hc hag

/-- A sequence of computations with finitely many outcomes has finitely
many. -/
theorem bind {x : ExceptT Stuck (TraceM (Step (Act E Ans)) σ) α}
    {f : α → ExceptT Stuck (TraceM (Step (Act E Ans)) σ) β} (hx : ExceptStepFinite x)
    (hf : ∀ a, ExceptStepFinite (f a)) : ExceptStepFinite (x >>= f) := fun s ans => by
  obtain ⟨L, hL⟩ := hx s ans
  obtain ⟨C, hC⟩ := List.exists_cover (L := L)
    (P := fun (p : α × List (Step (Act E Ans)) × σ) (q : β × List (Step (Act E Ans)) × σ) =>
      (f p.1).run p.2.2 (.ok (.ok q.1, q.2.1, q.2.2)) ∧
      Act.Agrees (fun i => ans ((Step.actsOf p.2.1).length + i)) (Step.actsOf q.2.1))
    fun p _ => by
      obtain ⟨C, hC⟩ := hf p.1 p.2.2 fun i => ans ((Step.actsOf p.2.1).length + i)
      exact ⟨C, fun q hq => hC _ _ _ hq.1 hq.2⟩
  refine ⟨L.flatMap fun p => C.map fun q => (q.1, p.2.1 ++ q.2.1, q.2.2), fun b mt s' h hag => ?_⟩
  rcases (TraceM.run_except_bind _ _ _ _).1 h with
    ⟨a, t, s₁, e', hx', hf', he⟩ | ⟨_, _, _, _, he⟩ | ⟨_, _, _, he⟩
  · rcases e' with ⟨_, _⟩ | ⟨y, t₁, s₂⟩
    · cases he
    simp only [TraceEnd.after, Except.ok.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    simp only [Step.actsOf, List.flatMap_append] at hag
    obtain ⟨hag₁, hag₂⟩ := Act.agrees_append.1 hag
    have hp := hL _ _ _ hx' hag₁
    exact List.mem_flatMap.2 ⟨_, hp, List.mem_map.2 ⟨(b, t₁, s'), hC _ hp _ ⟨hf', hag₂⟩, rfl⟩⟩
  · cases he
  · cases he

end ExceptStepFinite

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-- A run in a call's frame has its ops' outcomes, its frame left. -/
theorem ExceptStepFinite.inFrame {x : ExceptT Stuck (TraceM (Step (Act E Ans)) (TraceState Mem unit)) α}
    (h : ExceptStepFinite x) : ExceptStepFinite (inFrame x) := fun s ans => by
  obtain ⟨L, hL⟩ := h { s with mem := s.mem.enter } ans
  refine ⟨L.map fun p => (p.1, p.2.1, { p.2.2 with mem := p.2.2.mem.exit }), fun a mt s' hx hag => ?_⟩
  obtain ⟨e', he', he⟩ := (TraceM.run_inFrame _ _ _).1 hx
  rcases e' with ⟨_, _⟩ | ⟨y, t, s₁⟩
  · cases he
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  exact List.mem_map.2 ⟨_, hL _ _ _ he' hag, rfl⟩

/-! # Runs of ops at one budget -/

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (TraceM (Step (Act E Ans)) (TraceState Mem unit))]
  [DialectExtCall d (TraceM (Step (Act E Ans)) (TraceState Mem unit))]

/-- A traced run of ops at one budget has finitely many outcomes, given the
world's answers, from any environment and traced state, calls and recursion
included, when every op that runs by its own rule has finitely many. -/
theorem Func.traceOps_finite (hfin : OpsStepFinite d E Ans (TraceState Mem unit)) (M : Module d)
    (n : Nat) : ∀ (f : Func d) (env : Env d) (os : List (Operation d)),
      ExceptStepFinite (Func.runOps (m := TraceM (Step (Act E Ans)) (TraceState Mem unit)) M n f env os) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f env os
    match n, os with
    | 0, _ => simp only [Func.runOps]; exact ExceptStepFinite.pure _
    | _ + 1, [] => simp only [Func.runOps]; exact ExceptStepFinite.liftExcept _
    | n + 1, o :: os =>
      simp only [Func.runOps]
      all_goals repeat' (first
        | exact ExceptStepFinite.pure _
        | exact ExceptStepFinite.liftExcept _
        | exact ih _ (by omega) _ _ _
        | exact ExceptStepFinite.inFrame (ih _ (by omega) _ _ _)
        | (refine ExceptStepFinite.bind ?_ fun _ => ?_)
        | split)
      all_goals apply ExceptStepFinite.lift
      all_goals first
        | exact (hfin.1 _ (.inl ‹_›) _).2 ‹_›
        | exact (hfin.1 _ (.inr ‹_›) _).1 (by simpa using ‹¬isTerminator o.op = true›)
        | exact hfin.2 _ _ _

end Fir
