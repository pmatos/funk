import FirTest.TraceCalleeDiverge

/-!
A test of divergence inside a replaced callee over the traced runs of a dialect
with events (ADR-2026-11-09-1540, stage 3c-2b of #233), on the toy dialect
with calls of `FirTest.TraceCallDialect`. In `ubModule`, the callee `@h` hits
UB at once, and `@caller` calls it, then returns. Replace the body of `@h` by
one that jumps back to itself forever, showing nothing:

* the new `@h` refines the old one from every traced state: the old one's UB
  after no act allows anything;
* `@caller` diverges silently in the new module, inside its call of `@h`: its
  branch of moves enters `@h`, then jumps back forever, so the target's callee
  never returns;
* so congruence in the callee gives a traced outcome of `@caller` in the old
  module that allows that divergence.

The tests of `FirTest.TraceCalleeDiverge` only replace a callee that returns,
so none of their target's moves enters a callee and stays there.
-/

namespace FirTest.TraceCalleeEnter

open Fir Fir.Memory FirTest.TraceDialect FirTest.TraceCallDialect FirTest.TraceCalleeRefine
  FirTest.TraceCalleeDiverge

/-- The callee `@h`: UB at once. -/
def h : Func CallDialect where
  name := "h"
  params := []
  results := []
  body := { blocks := [{ label := "entry", params := [], body := [mkOp .ub] }] }

/-- The new body of `@h`: jump back to itself, forever, showing nothing. -/
def loopBody : Region CallDialect :=
  { blocks := [{ label := "loop", params := [], body := [brLoop] }] }

/-- A caller that calls `@h`, then returns. -/
def caller : Func CallDialect where
  name := "caller"
  params := []
  results := []
  body := { blocks := [{ label := "entry", params := [], body := [mkOp (.call "h"), mkOp .ret] }] }

/-- The module of the callee `@h` and its caller. -/
def ubModule : Module CallDialect :=
  { items := [.func h, .func caller], locs := [(0, .unknown)] }

/-- The module with `@h`'s body replaced by the loop. -/
abbrev loopModule : Module CallDialect := ubModule.replaceBody h.name loopBody

/-- The new `@h`. -/
abbrev h' : Func CallDialect := h.replaceBody h.name loopBody

/-- The symbols of `ubModule` are unique. -/
theorem nodup : (ubModule.funcs.map (·.name)).Nodup := by decide

/-- `@h` is a function of `ubModule`. -/
theorem h_mem : h ∈ ubModule.funcs := List.mem_cons_self

/-- `@caller` is a function of `ubModule`. -/
theorem caller_mem : caller ∈ ubModule.funcs := List.mem_cons_of_mem _ List.mem_cons_self

/-- The new module names the new `@h` by `@h`. -/
theorem new_h : loopModule.func? "h" = some h' := Module.func?_replaceBody_self nodup h_mem loopBody

/-- `ub` ends, in the traced layer of marked traces, in UB after its step. -/
theorem step_ub (s : St) : stepSem.denote CallOp.ub .nil s (.error ("ub", [.tick])) :=
  (TraceM.bind_apply _ _ _ _).2 (.inl ⟨(), [.tick], s, _, rfl, ⟨.error ("ub", []), rfl, rfl⟩, rfl⟩)

/-- The old `@h` hits UB at the budget `1` from every traced state, after its
step and no act. -/
theorem h_ub (s : St) :
    h.traceRunsFrom lay Empty.elim RunItems.empty ubModule (.nil, s) 1
      (.error ("ub", ([.tick] : List (Step (DialectTrace.Acts CallDialect))))) := by
  letI := stepSem
  have hops : Func.traceOps (Step (DialectTrace.Acts CallDialect)) ubModule 1 h [] [mkOp .ub]
      { s with mem := s.mem.enter } (.error ("ub", [.tick])) :=
    (Func.tStepPath_iff (TraceEnd.notStuck_error _ _)).2
      (.denoteUB (args := .nil) rfl rfl rfl rfl (step_ub _))
  exact Func.traceFrom_ub_iff.2 ⟨_, _, rfl, (TraceM.run_inFrame _ _ _).2 ⟨_, hops, rfl⟩⟩

/-- The old `@h` is refined by the new one, from every traced state: its UB
after no act allows whatever the new one does. -/
theorem h_isRefinedBy :
    h.traceRunsFrom lay Empty.elim RunItems.empty ubModule ⊑
      h'.traceRunsFrom lay Empty.elim RunItems.empty loopModule := by
  rintro ⟨a, s⟩ t' -
  cases a
  exact ⟨.ub [] "ub", ⟨1, _, h_ub s, rfl⟩, fun _ _ hi => by simp at hi⟩

/-! # `@caller` diverges inside the new `@h` -/

/-- `@caller` at its call of `@h`. -/
abbrev c₀ (s : St) : TCfg CallDialect Unit (unitsOf lay) :=
  ⟨caller, [], [mkOp (.call "h"), mkOp .ret], s⟩

/-- The new `@h` at its jump back. -/
abbrev l (s : St) : TCfg CallDialect Unit (unitsOf lay) := ⟨h', [], [brLoop], s⟩

/-- `@caller`'s configurations: the call, then the new `@h`'s jump back,
forever, in the frame of the call. -/
def cs (s : St) : Nat → TCfg CallDialect Unit (unitsOf lay)
  | 0 => c₀ s
  | _ + 1 => l { s with mem := s.mem.enter }

/-- The marked traces of those moves: none to enter `@h`, then a step for each
jump back. -/
def ct : Nat → List (Step (DialectTrace.Acts CallDialect))
  | 0 => []
  | _ + 1 => [.tick]

/-- `@caller` enters the new `@h`, which jumps back forever. -/
theorem caller_moves (s : St) (i : Nat) :
    letI := stepSem
    TCfg.Move (DialectTrace.Acts CallDialect) loopModule (cs s i) (cs s (i + 1)) (ct i) 1 := by
  letI := stepSem
  cases i with
  | zero =>
    exact .enter (args := .nil) (o := mkOp (.call "h")) rfl rfl rfl rfl new_h rfl
  | succ i =>
    exact .goto (args := .nil) (i := 0) (env₁ := []) (b := ⟨"loop", [], [brLoop]⟩) rfl rfl rfl rfl
      ((step_pure _ _ _).2 rfl) rfl

/-- `@caller` in the new module diverges silently after no act. -/
theorem caller_diverges :
    traceObservable (caller.traceRuns lay Empty.elim RunItems.empty (fun _ => ()) AddrRule.ignore
      loopModule .nil) (.diverge []) := by
  letI := stepSem
  have hb := TBranch.tShows (R := fun i => (cs { s₀ with mem := s₀.mem.enter } i).exh _ loopModule)
    (fun i => (caller_moves _ i).tStep (DialectTrace.stepAt_oneStep lay Empty.elim RunItems.empty)) 0
  rw [acts_silent fun i => by cases i <;> rfl] at hb
  have hb' := hb.congr (TCfg.exh_iff_traceFrom (M := loopModule) (g := caller) (a := .nil)
    (s := s₀) rfl)
  exact (Func.traceRuns_diverge_iff_from lay Empty.elim RunItems.empty _ _).2 (diverge_of_tShows hb')

/-! # The source allows it -/

/-- Replacing `@h`'s body by the loop refines every function of `ubModule` over
the spec's traced runs, divergence inside the new `@h` included. -/
theorem replace_isRefinedBy {f : Func CallDialect} (hf : f ∈ ubModule.funcs) :
    f.observedRuns lay Empty.elim RunItems.empty (fun _ => ()) ubModule ⊑
      (f.replaceBody h.name loopBody).observedRuns lay Empty.elim RunItems.empty (fun _ => ())
        loopModule :=
  Func.traceRuns_replaceBody_isRefinedBy lay Empty.elim RunItems.empty (fun _ => ())
    AddrRule.ignore call_traceFinite (fun g _ => traceOpsMonotone g) Core.Ty.isRefinedBy_refl
    Core.Ty.isRefinedBy_trans (fun h₁ h₂ => h₁.trans h₂) nodup h_mem loopBody h_isRefinedBy hf

/-- So `@caller`'s silent divergence inside the new `@h` is allowed by its traced
runs around the old one. -/
example : ∃ t, traceObservable (caller.observedRuns lay Empty.elim RunItems.empty (fun _ => ())
    ubModule .nil) t ∧
    t ⊑ (.diverge [] : TOutcome (DialectTrace.Acts CallDialect)
      (ObservedEnd (unitsOf lay) (fun _ => ()) (List (DVal CallDialect)))) :=
  replace_isRefinedBy caller_mem .nil _ caller_diverges

end FirTest.TraceCalleeEnter
