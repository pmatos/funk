import FirTest.TraceCalleeRefine

/-!
Tests of divergence across a replaced callee over the traced runs of a dialect
with events (ADR-2026-11-09-1540, stage 3c-2 of #233), on the toy dialect with
calls of `FirTest.TraceCallDialect`. In `callModule`, replace the body of `@g`
by the new one, which takes one step fewer and refines it
(`FirTest.TraceCalleeRefine`). Then:

* `@quiet`, which calls `@g` and jumps back forever, diverges silently in the
  new module, and its divergence is allowed by its traced runs in the old;
* `@loud`, which also emits on every round, shows the act of `emit`, answered
  `0`, forever in the new module, and that is allowed too.

Each target's divergence is shown by a branch of moves that repeats
(`TBranch.tShows`): the call of `@g`, which returns, then `emit` for `@loud`,
then the jump back.
-/

namespace FirTest.TraceCalleeDiverge

open Fir Fir.Memory FirTest.TraceDialect FirTest.TraceCallDialect FirTest.TraceCalleeRefine

/-- The symbols of `callModule` are unique. -/
theorem nodup : (callModule.funcs.map (·.name)).Nodup := by decide

/-- `@g` is a function of `callModule`. -/
theorem g_mem : g ∈ callModule.funcs := List.mem_cons_self

/-- The new module names the new `@g` by `@g`. -/
theorem new_g : newModule.func? "g" = some g' := Module.func?_replaceBody_self nodup g_mem newBody

/-- In the new module, from any traced state, a call of `@g` returns at the
budget `1`, after its one step, in that traced state. -/
theorem g'_ret (s : St) :
    letI := stepSem
    Func.traceCall (Step (DialectTrace.Acts CallDialect)) newModule 1 g' [] [mkOp .ret] s
      (.ok (.ok (.ret ([], 0)), [.tick], s)) := by
  letI := stepSem
  have h := (retOps_iff (M := newModule) (f := g') rfl (n := 1) (s := { s with mem := s.mem.enter })
    (TraceEnd.notStuck_ok _ _ _)).2 (.inr ⟨0, rfl, rfl⟩)
  exact (TraceM.run_inFrame _ _ _).2 ⟨_, h, by cases s; rfl⟩

/-- The marked trace of one step shows no act. -/
theorem actsOf_tick : Step.actsOf ([.tick] : List (Step (DialectTrace.Acts CallDialect))) = [] := rfl

/-- A run that shows the empty stream at every budget diverges silently after
no act. -/
theorem diverge_of_tShows {R : Nat → TRun (DialectTrace.Acts CallDialect)
    (List (DVal CallDialect) × St)} {K : Nat → Nat} (h : TShows (TRun.exh R) (fun _ => none) K) :
    traceObservable R (.diverge []) := by
  obtain ⟨t, ht, hdiv, hact⟩ := h.toObservable fun _ h => nomatch h
  match t, hdiv, hact with
  | .diverge tr, _, hact =>
    have : tr = [] := List.eq_nil_of_length_eq_zero (by
      have := hact 0
      simp only [TOutcome.act?] at this
      exact Nat.le_zero.1 (Nat.le_of_not_lt fun hl => by
        rw [List.getElem?_eq_getElem hl] at this
        cases this))
    exact this ▸ ht
  | .reacts _, _, hact => cases hact 0

/-! # `@quiet` diverges silently -/

/-- `@quiet` at its call of `@g`. -/
abbrev q₀ (s : St) : TCfg CallDialect Unit (unitsOf lay) := ⟨quiet, [], [mkOp (.call "g"), brLoop], s⟩

/-- `@quiet` at its jump back. -/
abbrev q₁ (s : St) : TCfg CallDialect Unit (unitsOf lay) := ⟨quiet, [], [brLoop], s⟩

/-- `@quiet`'s configurations: the call, then the jump back, forever. -/
def qs (s : St) (i : Nat) : TCfg CallDialect Unit (unitsOf lay) := if i % 2 = 0 then q₀ s else q₁ s

/-- `@quiet` goes on by the call of `@g`, which returns, then by the jump back,
forever. -/
theorem quiet_moves (s : St) (i : Nat) :
    letI := stepSem
    TCfg.Move (DialectTrace.Acts CallDialect) newModule (qs s i) (qs s (i + 1)) [.tick]
      (if i % 2 = 0 then 2 else 1) := by
  letI := stepSem
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · have h' : (i + 1) % 2 = 1 := by omega
    rw [show qs s i = q₀ s by simp [qs, h], show qs s (i + 1) = q₁ s by simp [qs, h'],
      show (if i % 2 = 0 then 2 else 1) = 2 by simp [h]]
    exact .ret (args := .nil) (U := 1) rfl rfl rfl rfl new_g g'_enter (g'_ret s) rfl rfl
  · have h' : (i + 1) % 2 = 0 := by omega
    rw [show qs s i = q₁ s by simp [qs, h], show qs s (i + 1) = q₀ s by simp [qs, h'],
      show (if i % 2 = 0 then 2 else 1) = 1 by simp [h]]
    exact .goto (args := .nil) (i := 0) (env₁ := [])
      (b := ⟨"loop", [], [mkOp (.call "g"), brLoop]⟩) rfl rfl rfl rfl ((step_pure _ _ _).2 rfl) rfl

/-- `@quiet` in the new module diverges silently after no act. -/
theorem quiet_diverges :
    traceObservable (quiet.traceRuns lay Empty.elim RunItems.empty (fun _ => ()) AddrRule.ignore
      newModule .nil) (.diverge []) := by
  letI := stepSem
  have hb := TBranch.tShows (R := fun i => (qs { (TraceState.init : St) with
      mem := (TraceState.init : St).mem.enter } i).exh _ newModule)
    (fun i => (quiet_moves _ i).tStep (DialectTrace.stepAt_oneStep lay Empty.elim RunItems.empty)) 0
  have hnone : TBranch.acts (fun _ => ([.tick] : List (Step (DialectTrace.Acts CallDialect)))) 0 =
      fun _ => none := by
    have hpre : ∀ j i, Step.actsOf (TBranch.pre (fun _ => ([.tick] : List (Step
        (DialectTrace.Acts CallDialect)))) i j) = [] := by
      intro j
      induction j with
      | zero => intro i; rfl
      | succ j ih => intro i; simp only [TBranch.pre, TGood.Sees.actsOf_append, actsOf_tick, ih]; rfl
    funext p
    cases ha : TBranch.acts (fun _ => ([.tick] : List (Step (DialectTrace.Acts CallDialect)))) 0 p with
    | none => rfl
    | some a =>
      obtain ⟨j, hj⟩ := TBranch.acts_some ha
      rw [hpre] at hj
      cases hj
  rw [hnone] at hb
  have hb' := hb.congr (TCfg.exh_iff_traceFrom (M := newModule) (g := quiet) (a := .nil)
    (s := TraceState.init) rfl)
  exact (Func.traceRuns_diverge_iff_from lay Empty.elim RunItems.empty _ _).2 (diverge_of_tShows hb')

/-! # `@loud` shows an act forever -/

/-- The act of `emit`, answered `0`. -/
abbrev act₀ : DialectTrace.Acts CallDialect := Act.mk (E := Nat) (Ans := Nat) 0 0

/-- `@loud` at its call of `@g`. -/
abbrev l₀ (s : St) : TCfg CallDialect Unit (unitsOf lay) :=
  ⟨loud, [], [mkOp (.call "g"), mkOp .emit, brLoop], s⟩

/-- `@loud` at its `emit`. -/
abbrev l₁ (s : St) : TCfg CallDialect Unit (unitsOf lay) := ⟨loud, [], [mkOp .emit, brLoop], s⟩

/-- `@loud` at its jump back. -/
abbrev l₂ (s : St) : TCfg CallDialect Unit (unitsOf lay) := ⟨loud, [], [brLoop], s⟩

/-- `@loud`'s configurations: the call, `emit`, then the jump back, forever. -/
def ls (s : St) (i : Nat) : TCfg CallDialect Unit (unitsOf lay) :=
  if i % 3 = 0 then l₀ s else if i % 3 = 1 then l₁ s else l₂ s

/-- The marked traces of `@loud`'s moves: a step, then `emit`'s step and act. -/
def lt (i : Nat) : List (Step (DialectTrace.Acts CallDialect)) :=
  if i % 3 = 1 then [.tick, .act act₀] else [.tick]

/-- `@loud` goes on by the call of `@g`, which returns, then by `emit`,
answered `0`, then by the jump back, forever. -/
theorem loud_moves (s : St) (i : Nat) :
    letI := stepSem
    TCfg.Move (DialectTrace.Acts CallDialect) newModule (ls s i) (ls s (i + 1)) (lt i)
      (if i % 3 = 0 then 2 else 1) := by
  letI := stepSem
  rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with h | h | h
  · have h' : (i + 1) % 3 = 1 := by omega
    rw [show ls s i = l₀ s by simp [ls, h], show ls s (i + 1) = l₁ s by simp [ls, h'],
      show lt i = [.tick] by simp [lt, h], show (if i % 3 = 0 then 2 else 1) = 2 by simp [h]]
    exact .ret (args := .nil) (U := 1) rfl rfl rfl rfl new_g g'_enter (g'_ret s) rfl rfl
  · have h' : (i + 1) % 3 = 2 := by omega
    rw [show ls s i = l₁ s by simp [ls, h], show ls s (i + 1) = l₂ s by simp [ls, h'],
      show lt i = [.tick, .act act₀] by simp [lt, h], show (if i % 3 = 0 then 2 else 1) = 1 by simp [h]]
    exact .denote (args := .nil) (rs := .nil) rfl rfl rfl rfl (step_emit .nil s 0) rfl
  · have h' : (i + 1) % 3 = 0 := by omega
    rw [show ls s i = l₂ s by simp [ls, h], show ls s (i + 1) = l₀ s by simp [ls, h'],
      show lt i = [.tick] by simp [lt, h], show (if i % 3 = 0 then 2 else 1) = 1 by simp [h]]
    exact .goto (args := .nil) (i := 0) (env₁ := [])
      (b := ⟨"loop", [], [mkOp (.call "g"), mkOp .emit, brLoop]⟩) rfl rfl rfl rfl
      ((step_pure _ _ _).2 rfl) rfl

/-- `@loud`'s moves show the act of `emit`, answered `0`, and nothing else. -/
theorem lt_acts : ∀ j i a, a ∈ Step.actsOf (TBranch.pre lt i j) → a = act₀ := by
  intro j
  induction j with
  | zero => intro i a h; simp [TBranch.pre, Step.actsOf] at h
  | succ j ih =>
    intro i a h
    simp only [TBranch.pre, TGood.Sees.actsOf_append, List.mem_append] at h
    rcases h with h | h
    · unfold lt at h
      split at h <;> simp [Step.actsOf, Step.acts] at h
      exact h
    · exact ih _ _ h

/-- Every three moves, `@loud` shows one more act. -/
theorem lt_many : ∀ q, q ≤ (Step.actsOf (TBranch.pre lt 0 (3 * q))).length := by
  intro q
  induction q with
  | zero => exact Nat.zero_le _
  | succ q ih =>
    rw [show 3 * (q + 1) = 3 * q + 1 + 1 + 1 by omega, TBranch.pre_succ, TBranch.pre_succ,
      TBranch.pre_succ]
    have h1 : lt (0 + (3 * q + 1)) = [.tick, .act act₀] := by
      simp only [lt, Nat.zero_add, ite_eq_left_iff]
      omega
    simp only [TGood.Sees.actsOf_append, List.length_append, h1]
    have : (Step.actsOf ([.tick, .act act₀] : List (Step (DialectTrace.Acts CallDialect)))).length
      = 1 := rfl
    omega

/-- `@loud` in the new module shows the act of `emit`, answered `0`,
forever. -/
theorem loud_reacts :
    traceObservable (loud.traceRuns lay Empty.elim RunItems.empty (fun _ => ()) AddrRule.ignore
      newModule .nil) (.reacts fun _ => act₀) := by
  letI := stepSem
  have hb := TBranch.tShows (R := fun i => (ls { (TraceState.init : St) with
      mem := (TraceState.init : St).mem.enter } i).exh _ newModule)
    (fun i => (loud_moves _ i).tStep (DialectTrace.stepAt_oneStep lay Empty.elim RunItems.empty)) 0
  have hall : TBranch.acts lt 0 = fun _ => some act₀ := by
    funext p
    have := lt_many (p + 1)
    obtain ⟨b, hb⟩ : ∃ b, (Step.actsOf (TBranch.pre lt 0 (3 * (p + 1))))[p]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [TBranch.acts_eq hb, lt_acts _ _ _ (List.mem_of_getElem? hb)]
  rw [hall] at hb
  have hb' := hb.congr (TCfg.exh_iff_traceFrom (M := newModule) (g := loud) (a := .nil)
    (s := TraceState.init) rfl)
  obtain ⟨t, ht, hdiv, hact⟩ := hb'.toObservable fun _ _ => rfl
  refine (Func.traceRuns_reacts_iff_from lay Empty.elim RunItems.empty _ _).2 ?_
  match t, hdiv, hact with
  | .reacts T, _, hact =>
    have : T = fun _ => act₀ := funext fun i => Option.some.inj (hact i)
    exact this ▸ ht
  | .diverge tr, _, hact =>
    have := hact tr.length
    simp [TOutcome.act?] at this

/-! # The source allows both -/

/-- `@quiet` is a function of `callModule`. -/
theorem quiet_mem : quiet ∈ callModule.funcs := List.mem_cons_of_mem _ List.mem_cons_self

/-- `@loud` is a function of `callModule`. -/
theorem loud_mem : loud ∈ callModule.funcs :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- Replacing `@g`'s body refines every function of `callModule` over the
spec's traced runs, divergence included. -/
theorem replace_isRefinedBy {f : Func CallDialect} (hf : f ∈ callModule.funcs) :
    f.observedRuns lay Empty.elim RunItems.empty (fun _ => ()) callModule ⊑
      (f.replaceBody g.name newBody).observedRuns lay Empty.elim RunItems.empty (fun _ => ())
        newModule :=
  Func.traceRuns_replaceBody_isRefinedBy lay Empty.elim RunItems.empty (fun _ => ())
    AddrRule.ignore call_traceFinite (fun g _ => traceOpsMonotone g) Core.Ty.isRefinedBy_refl
    Core.Ty.isRefinedBy_trans (fun h₁ h₂ => h₁.trans h₂) nodup g_mem newBody g_isRefinedBy hf

/-- So `@quiet`'s silent divergence around the new `@g` is allowed by its
traced runs around the old one. -/
example : ∃ t, traceObservable (quiet.observedRuns lay Empty.elim RunItems.empty (fun _ => ())
    callModule .nil) t ∧
    t ⊑ (.diverge [] : TOutcome (DialectTrace.Acts CallDialect)
      (ObservedEnd (unitsOf lay) (fun _ => ()) (List (DVal CallDialect)))) :=
  replace_isRefinedBy quiet_mem .nil _ quiet_diverges

/-- And `@loud`'s act forever around the new `@g` is allowed by its traced runs
around the old one. -/
example : ∃ t, traceObservable (loud.observedRuns lay Empty.elim RunItems.empty (fun _ => ())
    callModule .nil) t ∧
    t ⊑ (.reacts (fun _ => act₀) : TOutcome (DialectTrace.Acts CallDialect)
      (ObservedEnd (unitsOf lay) (fun _ => ()) (List (DVal CallDialect)))) :=
  replace_isRefinedBy loud_mem .nil _ loud_reacts

end FirTest.TraceCalleeDiverge
