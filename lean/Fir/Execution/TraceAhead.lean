import Fir.Execution.TraceStepPaths

/-!
# More fuel, in the traced layer

A traced run with more fuel takes the same paths as one with less, further
(`Fir.Execution.TraceTruncate` cuts a path down to less fuel). Going up is
simpler, and holds in every traced layer: with `j` more steps of fuel, from
the same environment and traced state,

* each return of a run of ops is a return with the same values, acts and
  traced state, that leaves `j` more steps;
* each UB is UB after the same acts.

The proof follows the ways a step goes on, by strong induction on the
budget. A call's callee returns with `j` more steps left, so the caller goes
on with `j` more steps too. The theorems with memory say the same of runs
with memory (`Fir.Execution.MemoryMonotone`). Congruence in the callee over
traced runs needs it: the source's callee may return at one budget and the
rest of the source's run end at another, and the whole ends at their sum.
-/

namespace Fir

open Memory

variable {B : Type} {σ : Type} {V : Type}

/-- A way of ending is _done_: a return or UB. Running out of fuel and being
stuck are not. -/
def TraceEnd.Done : TraceEnd B σ (Except Stuck (Result (V × Nat))) → Prop
  | .ok (.ok (.ret _), _, _) => True
  | .error _ => True
  | _ => False

/-- A way of ending with `j` more steps left on a return. -/
def TraceEnd.addLeft (j : Nat) :
    TraceEnd B σ (Except Stuck (Result (V × Nat))) → TraceEnd B σ (Except Stuck (Result (V × Nat)))
  | .ok (.ok (.ret (v, k)), t, s) => .ok (.ok (.ret (v, k + j)), t, s)
  | e => e

/-- A way of ending that is done is not stuck. -/
theorem TraceEnd.Done.notStuck : ∀ {e : TraceEnd B σ (Except Stuck (Result (V × Nat)))},
    e.Done → TraceEnd.NotStuck e
  | .ok (.ok (.ret _), _, _), _ => TraceEnd.notStuck_ok _ _ _
  | .error _, _ => TraceEnd.notStuck_error _ _

/-- A way of ending done after a trace is done before it. -/
theorem TraceEnd.Done.of_after {t : List B} :
    ∀ {e : TraceEnd B σ (Except Stuck (Result (V × Nat)))}, (e.after t).Done → e.Done
  | .ok (.ok (.ret _), _, _), _ | .error _, _ => trivial

/-- More steps left keep a way of ending done. -/
theorem TraceEnd.Done.addLeft (j : Nat) : ∀ {e : TraceEnd B σ (Except Stuck (Result (V × Nat)))},
    e.Done → (e.addLeft j).Done
  | .ok (.ok (.ret _), _, _), _ | .error _, _ => trivial

/-- No more steps left leave a way of ending as it is. -/
theorem TraceEnd.addLeft_zero :
    ∀ e : TraceEnd B σ (Except Stuck (Result (V × Nat))), e.addLeft 0 = e
  | .ok (.ok (.ret _), _, _) | .ok (.ok .fuelExhausted, _, _) | .ok (.error _, _, _)
  | .error _ => rfl

/-- Adding steps left commutes with a trace before. -/
theorem TraceEnd.addLeft_after (j : Nat) (t : List B) :
    ∀ e : TraceEnd B σ (Except Stuck (Result (V × Nat))),
      (e.after t).addLeft j = (e.addLeft j).after t
  | .ok (.ok (.ret _), _, _) | .ok (.ok .fuelExhausted, _, _) | .ok (.error _, _, _)
  | .error _ => rfl

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-- Adding steps left commutes with leaving a frame. -/
theorem TraceEnd.addLeft_exit (j : Nat) :
    ∀ e : TraceEnd B (TraceState Mem unit) (Except Stuck (Result (V × Nat))),
      TraceEnd.addLeft j (e.map fun p => (p.1, p.2.1, ({ p.2.2 with mem := p.2.2.mem.exit } :
          TraceState Mem unit))) =
        (e.addLeft j).map fun p => (p.1, p.2.1, { p.2.2 with mem := p.2.2.mem.exit })
  | .ok (.ok (.ret _), _, _) | .ok (.ok .fuelExhausted, _, _) | .ok (.error _, _, _)
  | .error _ => rfl

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (TraceM B (TraceState Mem unit))] {M : Module d}

/-- Each return of a traced run of ops is a return of the run with `j` more
steps of fuel, from the same environment and traced state, that leaves `j`
more steps, after the same acts and in the same traced state; each UB is UB
of the run with more fuel, after the same acts. -/
theorem Func.traceOps_up (j n : Nat) :
    ∀ (f : Func d) (env : Env d) (os : List (Operation d)) (s : TraceState Mem unit) e,
      Func.traceOps B M n f env os s e → e.Done → Func.traceOps B M (n + j) f env os s (e.addLeft j) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f env os s e he hd
    have hne := hd.notStuck
    match n, os, he with
    | 0, _, he =>
      cases Func.traceOps_zero.1 he
      exact hd.elim
    | _ + 1, [], he => exact absurd he (Func.traceOps_nil hne)
    | n + 1, o :: os, he =>
      have ihn := ih n (Nat.lt_succ_self n)
      rw [Nat.add_right_comm]
      have mk : ∀ {x}, TraceEnd.NotStuck x → Func.TStepPath M (n + j) f env o os s x →
          Func.traceOps B M (n + j + 1) f env (o :: os) s x :=
        fun hx h => (Func.tStepPath_iff hx).2 h
      have call : ∀ {g : Func d} {genv : Env d} {body : List (Operation d)}
          {e₁ : TraceEnd B (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))},
          Func.traceCall B M n g genv body s e₁ → e₁.Done →
          Func.traceCall B M (n + j) g genv body s (e₁.addLeft j) := by
        intro g genv body e₁ h₁ hd₁
        obtain ⟨e₂, h₂, rfl⟩ := (TraceM.run_inFrame _ _ _).1 h₁
        have hd₂ : e₂.Done := by
          rcases e₂ with _ | ⟨_ | (_ | _), _, _⟩ <;> first | trivial | exact hd₁.elim
        rw [TraceEnd.addLeft_exit]
        exact (TraceM.run_inFrame _ _ _).2 ⟨_, ihn _ _ _ _ _ h₂ hd₂, rfl⟩
      cases (Func.tStepPath_iff hne).1 he with
      | exitUB hreg hargs hT hos hx =>
        exact mk (TraceEnd.notStuck_error _ _) (.exitUB hreg hargs hT hos hx)
      | ret hreg hargs hT hos hx hs =>
        exact mk (TraceEnd.notStuck_ok _ _ _) (.ret hreg hargs hT hos hx hs)
      | goto hreg hargs hT hos hx hj h =>
        rw [TraceEnd.addLeft_after]
        have h₁ := ihn _ _ _ _ _ h hd.of_after
        exact mk ((hd.of_after.addLeft j).notStuck.after)
          (.goto hreg hargs hT hos hx hj h₁)
      | denoteUB hreg hargs hT hc hx =>
        exact mk (TraceEnd.notStuck_error _ _) (.denoteUB hreg hargs hT hc hx)
      | denote hreg hargs hT hc hx hlen h =>
        rw [TraceEnd.addLeft_after]
        have h₁ := ihn _ _ _ _ _ h hd.of_after
        exact mk ((hd.of_after.addLeft j).notStuck.after)
          (.denote hreg hargs hT hc hx hlen h₁)
      | callUB hreg hargs hT hc hg hen hx =>
        exact mk (TraceEnd.notStuck_error _ _) (.callUB hreg hargs hT hc hg hen (call hx trivial))
      | callExh _ _ _ _ _ _ _ => exact hd.elim
      | callRet hreg hargs hT hc hg hen hx hty hlen h =>
        rw [TraceEnd.addLeft_after]
        have h₁ := ih _ (Nat.lt_succ_of_le (Nat.min_le_right _ _)) _ _ _ _ _ h hd.of_after
        rw [← Nat.add_min_add_right] at h₁
        exact mk ((hd.of_after.addLeft j).notStuck.after)
          (.callRet hreg hargs hT hc hg hen (call hx trivial) hty hlen h₁)

/-- Each return of a callee's ops in a call's frame is a return of its ops
with `j` more steps of fuel, leaving `j` more; each UB is UB there too. -/
theorem Func.traceCall_up (j n : Nat) {g : Func d} {genv : Env d} {body : List (Operation d)}
    {s : TraceState Mem unit} {e : TraceEnd B (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))}
    (h : Func.traceCall B M n g genv body s e) (hd : e.Done) :
    Func.traceCall B M (n + j) g genv body s (e.addLeft j) := by
  obtain ⟨e₂, h₂, rfl⟩ := (TraceM.run_inFrame _ _ _).1 h
  have hd₂ : e₂.Done := by
    rcases e₂ with _ | ⟨_ | (_ | _), _, _⟩ <;> first | trivial | exact hd.elim
  rw [TraceEnd.addLeft_exit]
  exact (TraceM.run_inFrame _ _ _).2 ⟨_, Func.traceOps_up j n _ _ _ _ _ h₂ hd₂, rfl⟩

end Fir
