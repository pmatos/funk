import Fir.Execution.TraceStepPaths
import Fir.Execution.TraceSteps

/-!
# Calls between two steps

In the traced layer of marked traces, each op that runs by its own rule shows
a step, and a call shows none: the ops of its callee show theirs
(`Fir.Execution.TraceDialect`). Each op, a call included, takes one step of
fuel. So the fuel that a run spends between two of its steps is the fuel of
the calls it makes before its next step. Divergence needs a bound on it, the
same for every path of every run of the module, so that a run cut at a
budget has taken a known number of steps.

The calls before a step form a _chain_. When the first op of the ops a run
goes on with calls a function of the module, the run enters that function's
entry block, whose first op may call another function, and so on, until an
op that runs by its own rule. The chain depends only on the module, not on
values: an op's callee is its symbol's function, and the callee starts at
its entry block. So each list of ops starts a chain of a fixed length, or
an endless one.

* _The bound._ A chain starting at a call goes on from the entry block of a
  function of the module, and there are finitely many of those. So the
  chains of the module have a largest length, and every list of ops starts
  a chain of at most one more call, or an endless one.
* _A cycle never shows a step again._ A list of ops that starts an endless
  chain calls, then calls again in the callee, forever: a path from it never
  returns, never hits UB, and shows nothing. It runs out of fuel or is
  stuck.
-/

namespace Fir

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]

/-! # Chains of calls -/

/-- The ops of the entry block of the function that the first of the ops
`os` calls, when it is an op that calls a function of the module `M` that
has an entry block. -/
def Module.callHead? (M : Module d) : List (Operation d) → Option (List (Operation d))
  | [] => none
  | o :: _ =>
    if isTerminator o.op then none
    else match callee? o.op with
      | none => none
      | some s => match M.func? s with
        | none => none
        | some g => g.blocks.head?.map (·.body)

/-- The ops `os` start a chain of `c` calls in the module `M`: `c` calls, each
the first op of its callee's entry block but the first, before an op that is
not a call of a function of the module with an entry block. -/
inductive Module.CallChain (M : Module d) : List (Operation d) → Nat → Prop
  | stop {os : List (Operation d)} : M.callHead? os = none → M.CallChain os 0
  | call {os body : List (Operation d)} {c : Nat} :
      M.callHead? os = some body → M.CallChain body c → M.CallChain os (c + 1)

variable {M : Module d}

omit [TyDenote d.Ty] [DecidableEq d.Ty] in
/-- A list of ops starts at most one chain. -/
theorem Module.CallChain.unique {os : List (Operation d)} {c c' : Nat} (h : M.CallChain os c)
    (h' : M.CallChain os c') : c = c' := by
  induction h generalizing c' with
  | stop hn =>
    cases h' with
    | stop _ => rfl
    | call hs _ => rw [hn] at hs; cases hs
  | call hs _ ih =>
    cases h' with
    | stop hn => rw [hn] at hs; cases hs
    | call hs' h' =>
      rw [hs] at hs'
      cases hs'
      rw [ih h']

omit [TyDenote d.Ty] [DecidableEq d.Ty] in
/-- A terminator starts no call. -/
theorem Module.callHead?_terminator {o : Operation d} (os : List (Operation d))
    (hT : isTerminator o.op = true) : M.callHead? (o :: os) = none := by
  simp [Module.callHead?, hT]

omit [TyDenote d.Ty] [DecidableEq d.Ty] in
/-- An op with no callee starts no call. -/
theorem Module.callHead?_noCallee {o : Operation d} (os : List (Operation d))
    (hc : callee? o.op = none) : M.callHead? (o :: os) = none := by
  simp [Module.callHead?, hc]

/-- A call of a function of the module that enters it starts a call of the
ops of its entry block. -/
theorem Module.callHead?_call {o : Operation d} (os : List (Operation d)) {sym : Name} {g : Func d}
    {dvs : List (DVal d)} {body : List (Operation d)} {genv : Env d}
    (hT : isTerminator o.op = false) (hc : callee? o.op = some sym) (hg : M.func? sym = some g)
    (hen : g.enter dvs = .ok (body, genv)) : M.callHead? (o :: os) = some body := by
  obtain ⟨e, he, -, -, hp⟩ := Func.enter_eq_ok hen
  cases hp
  simp [Module.callHead?, hT, hc, hg, he]

omit [TyDenote d.Ty] [DecidableEq d.Ty] in
/-- The chains of a module have a bound: some `W` exceeds the length of every
chain by at least one. -/
theorem Module.exists_callBound (M : Module d) :
    ∃ W, 0 < W ∧ ∀ os c, M.CallChain os c → c + 1 ≤ W := by
  have hg : ∀ g ∈ M.funcs, ∃ m, ∀ body c, g.blocks.head?.map (·.body) = some body →
      M.CallChain body c → c ≤ m := fun g _ => by
    by_cases h : ∃ body c, g.blocks.head?.map (·.body) = some body ∧ M.CallChain body c
    · obtain ⟨body, c, hb, hc⟩ := h
      refine ⟨c, fun body' c' hb' hc' => ?_⟩
      rw [hb] at hb'
      cases hb'
      exact Nat.le_of_eq (hc'.unique hc)
    · exact ⟨0, fun body c hb hc => absurd ⟨body, c, hb, hc⟩ h⟩
  obtain ⟨m, hm⟩ := List.exists_budget
    (Q := fun (g : Func d) m => ∀ body c, g.blocks.head?.map (·.body) = some body → M.CallChain body c → c ≤ m)
    (fun _ _ _ hle hq body c hb hc => Nat.le_trans (hq body c hb hc) hle) hg
  refine ⟨m + 2, by omega, fun os c h => ?_⟩
  cases h with
  | stop _ => omega
  | @call _ body c hs hc =>
    match os, hs with
    | o :: _, hs =>
      simp only [Module.callHead?] at hs
      split at hs
      · cases hs
      split at hs
      · cases hs
      split at hs
      · cases hs
      rename_i g hfg
      have := hm g (List.mem_of_find?_eq_some hfg) body c hs hc
      omega

/-! # A cycle never shows a step again -/

open Memory

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] {B : Type}
  [DialectDenote d (TraceM B (TraceState Mem unit))]

/-- A path that is not stuck of a traced run of ops that start no chain, an
endless one, runs out of fuel and shows nothing. -/
theorem Func.traceOps_silent (n : Nat) :
    ∀ (f : Func d) (env : Env d) (os : List (Operation d)) (s : TraceState Mem unit),
      (∀ c, ¬ M.CallChain os c) →
      ∀ e, Func.traceOps B M n f env os s e → TraceEnd.NotStuck e →
        ∃ s', e = .ok (.ok .fuelExhausted, [], s') := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f env os s hno e he hne
    match n, os, he with
    | 0, _, he => exact ⟨s, Func.traceOps_zero.1 he⟩
    | _ + 1, [], _ => exact absurd (Module.CallChain.stop rfl) (hno 0)
    | n + 1, o :: os, he =>
      have callee : ∀ {sym g genv body e₁}, isTerminator o.op = false → callee? o.op = some sym →
          M.func? sym = some g → ∀ {args : HVector toType (sig o.op)},
          g.enter args.toDVals = .ok (body, genv) → Func.traceCall B M n g genv body s e₁ →
          TraceEnd.NotStuck e₁ → ∃ s', e₁ = .ok (.ok .fuelExhausted, [], s') := by
        intro sym g genv body e₁ hT hc hg args hen h₁ hne₁
        have hno' : ∀ c, ¬ M.CallChain body c := fun c hch =>
          hno (c + 1) (.call (Module.callHead?_call os hT hc hg hen) hch)
        obtain ⟨e₂, h₂, rfl⟩ := (TraceM.run_inFrame _ _ _).1 h₁
        have hne₂ : TraceEnd.NotStuck e₂ := by
          rintro st t s₂ rfl
          exact hne₁ st t _ rfl
        obtain ⟨s', rfl⟩ := ih n (Nat.lt_succ_self n) g genv body _ hno' e₂ h₂ hne₂
        exact ⟨_, rfl⟩
      have stop : M.callHead? (o :: os) = none → False := fun h => hno 0 (.stop h)
      cases (Func.tStepPath_iff hne).1 he with
      | exitUB _ _ hT => exact (stop (Module.callHead?_terminator os hT)).elim
      | ret _ _ hT => exact (stop (Module.callHead?_terminator os hT)).elim
      | goto _ _ hT => exact (stop (Module.callHead?_terminator os hT)).elim
      | denoteUB _ _ _ hc => exact (stop (Module.callHead?_noCallee os hc)).elim
      | denote _ _ _ hc => exact (stop (Module.callHead?_noCallee os hc)).elim
      | callUB _ _ hT hc hg hen hx =>
        obtain ⟨_, h⟩ := callee hT hc hg hen hx (TraceEnd.notStuck_error _ _)
        cases h
      | callExh _ _ hT hc hg hen hx =>
        obtain ⟨_, h⟩ := callee hT hc hg hen hx (TraceEnd.notStuck_ok _ _ _)
        cases h
        exact ⟨_, rfl⟩
      | callRet _ _ hT hc hg hen hx =>
        obtain ⟨_, h⟩ := callee hT hc hg hen hx (TraceEnd.notStuck_ok _ _ _)
        cases h

end Fir
