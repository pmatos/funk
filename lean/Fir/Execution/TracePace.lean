import Fir.Execution.TraceChain
import Fir.Execution.TraceFinite

/-!
# The fuel of a return

In the traced layer of marked traces, let every path of every op and of
every external call show exactly one step, as it does when each op runs after a step
(`DialectTrace.stepAt_oneStep`), and let `W` exceed the length of every
chain of calls of the module by at least one (`Module.exists_callBound`).
Then a return of a run of ops spends fuel in proportion to its steps: a run
that starts with `n` steps of fuel and returns with `k` left, after a marked
trace of `m` steps, has

* spent at least one step of fuel on each step, so `k + m ≤ n`, and shown at
  least one step, its return's;
* spent at most `W` on each step but the first, and on the first the `c`
  calls of the chain that its ops start and the step itself:
  `n - k ≤ W (m - 1) + c + 1`.

The proof follows the ways a step goes on, by strong induction on the
budget. An op that runs by its own rule, or a call of an external
declaration, shows one step and spends one step of fuel, and the run goes on from ops whose chain is shorter than `W`. A
call spends one step of fuel and starts the chain of its callee's entry
block, one call longer; its callee returns, and the caller goes on.
-/

namespace Fir

open Memory

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] {A : Type}
  [DialectDenote d (TraceM (Step A) (TraceState Mem unit))]
  [DialectExtCall d (TraceM (Step A) (TraceState Mem unit))] {M : Module d}

/-- A return of a run of the ops `os` with `n` steps of fuel is paced by `W`:
it leaves `k` steps after a marked trace of `m` steps, with `k + m ≤ n`,
`0 < m`, and `n + W ≤ k + W m + c + 1`, where `os` starts a chain of `c`
calls. Other ways of ending are not constrained. -/
def TraceEnd.RetPaced (M : Module d) (W n : Nat) (os : List (Operation d)) :
    TraceEnd (Step A) (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat))) → Prop
  | .ok (.ok (.ret (_, k)), mt, _) => k + Step.ticks mt ≤ n ∧ 0 < Step.ticks mt ∧
      ∃ c, M.CallChain os c ∧ n + W ≤ k + W * Step.ticks mt + c + 1
  | _ => True

omit [DecidableEq d.Ty] [DecidableEq Mem] [DialectDenote d (TraceM (Step A) (TraceState Mem unit))]
    [DialectExtCall d (TraceM (Step A) (TraceState Mem unit))] in
/-- A return paced from the ops `os₁` with `m` steps, after the trace `t` of
one step, is paced from ops that start no call with `m + 1` steps. -/
theorem TraceEnd.RetPaced.after_step {W m : Nat} {os₁ os : List (Operation d)}
    (hW : ∀ os c, M.CallChain os c → c + 1 ≤ W) (hos : M.callHead? os = none)
    {t : List (Step A)} (ht : Step.ticks t = 1) :
    ∀ {e : TraceEnd (Step A) (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))},
      TraceEnd.RetPaced M W m os₁ e → TraceEnd.RetPaced M W (m + 1) os (e.after t)
  | .ok (.ok (.ret (_, k)), mt, _), ⟨h₁, _, c, hc, h₃⟩ => by
    have := hW _ _ hc
    refine ⟨?_, ?_, 0, .stop hos, ?_⟩ <;>
      simp only [Step.ticks_append, ht, Nat.mul_add, Nat.mul_one] <;> omega
  | .ok (.ok .fuelExhausted, _, _), _ | .ok (.error _, _, _), _ | .error _, _ => trivial

variable (A) in
/-- Every return of a traced run of ops is paced by `W`, when every path of
every op shows exactly one step and `W` exceeds the length of every chain of
calls of the module by at least one. -/
theorem Func.traceOps_retPaced (hone : OpsOneStep d A (TraceState Mem unit)) {W : Nat}
    (hW : ∀ os c, M.CallChain os c → c + 1 ≤ W) (n : Nat) :
    ∀ (f : Func d) (env : Env d) (os : List (Operation d)) (s : TraceState Mem unit) e,
      Func.traceOps (Step A) M n f env os s e → TraceEnd.NotStuck e →
        TraceEnd.RetPaced M W n os e := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f env os s e he hne
    match n, os, he with
    | 0, _, he =>
      cases Func.traceOps_zero.1 he
      trivial
    | _ + 1, [], he => exact absurd he (Func.traceOps_nil hne)
    | n + 1, o :: os, he =>
      cases (Func.tStepPath_iff hne).1 he with
      | exitUB => trivial
      | ret _ _ hT _ hx =>
        have ht := (hone.1 _ _ _).2 _ hx
        refine ⟨?_, ?_, 0, .stop (Module.callHead?_terminator os hT), ?_⟩ <;>
          simp only [TraceEnd.trace] at ht <;> simp only [ht] <;> omega
      | goto _ _ hT _ hx _ h =>
        exact (ih n (Nat.lt_succ_self n) _ _ _ _ _ h (TraceEnd.NotStuck.of_after hne)).after_step
          hW (Module.callHead?_terminator os hT) ((hone.1 _ _ _).2 _ hx)
      | denoteUB => trivial
      | denote _ _ _ hc hx _ h =>
        exact (ih n (Nat.lt_succ_self n) _ _ _ _ _ h (TraceEnd.NotStuck.of_after hne)).after_step
          hW (Module.callHead?_noCallee os hc) ((hone.1 _ _ _).1 _ hx)
      | extUB => trivial
      | ext _ _ hT hc hg _ hx _ _ h =>
        exact (ih n (Nat.lt_succ_self n) _ _ _ _ _ h (TraceEnd.NotStuck.of_after hne)).after_step
          hW (Module.callHead?_noFunc os hT hc hg) (hone.2 _ _ _ _ _ hx)
      | callUB => trivial
      | callExh => trivial
      | @callRet args sym g body genv vs k₁ tc s₁ e₂ _ _ hT hc hg hen hx _ _ h =>
        obtain ⟨e₁, h₁, he₁⟩ := (TraceM.run_inFrame _ _ _).1 hx
        rcases e₁ with ⟨_, _⟩ | ⟨y, t₁, s₂⟩
        · cases he₁
        simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at he₁
        obtain ⟨rfl, rfl, -⟩ := he₁
        obtain ⟨hk₁, hp₁, c₁, hc₁, hb₁⟩ := ih n (Nat.lt_succ_self n) _ _ _ _ _ h₁
          (TraceEnd.notStuck_ok _ _ _)
        have hmin : min k₁ n = k₁ := Nat.min_eq_left (by omega)
        rw [hmin] at h
        have hW₁ := hW _ _ hc₁
        have hcall := Module.CallChain.call (Module.callHead?_call os hT hc hg hen) hc₁
        rcases e₂ with ⟨_, _⟩ | ⟨y₂, t₂, s₃⟩
        · trivial
        rcases y₂ with _ | (⟨vs₂, k₂⟩ | _)
        · trivial
        · obtain ⟨hk₂, -, c₂, hc₂, hb₂⟩ := ih k₁ (by omega) _ _ _ _ _ h (TraceEnd.notStuck_ok _ _ _)
          have hW₂ := hW _ _ hc₂
          refine ⟨?_, ?_, c₁ + 1, hcall, ?_⟩ <;>
            simp only [Step.ticks_append, Nat.mul_add] <;> omega
        · trivial

end Fir
