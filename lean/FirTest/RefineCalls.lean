import Fir.Core.MemoryCallRefine
import FirTest.RunsCalls

/-!
Tests of #20's two function-level refinement theorems, applied to valid
modules with calls and recursion, which shows that their hypotheses can
be met, and the axioms of their proofs.

* Refined arguments, with memory: `@fact`, which calls itself, on a poison
  argument is refined by `@fact` on `5`; and `@even`, which calls `@odd`,
  which calls it back, on any arguments is refined by itself on refined
  ones.
* Congruence in the callee, with memory, for a callee that touches no
  memory, wherever a run names the core's memories: `@g` divides by zero
  before it calls itself, so it hits UB on every argument, and every body
  refines it. `@count` calls `@g` and itself. With a new body for `@g`,
  which calls `@count` back, the module is still valid, and each of its
  functions is refined by its counterpart: `@count` hits UB in the old
  module and runs out of fuel in the new. Every call of either module names
  one of its functions, so no summary touches memory. A second instance
  gives `@odd` its own body, in the mutual recursion of `@even` and `@odd`.
* Congruence in the callee from given memories is tested in
  `FirTest.RefineCallsFrom`.
-/

namespace FirTest

open Fir Core Example

/-! # Refined arguments -/

/-- `@fact` on a poison argument is refined by `@fact` on `5`, with memory. -/
theorem fact_args :
    observable (factFn.memRuns recModule.layout.entry id recModule (.cons .poison .nil)) ⊑
      observable (factFn.memRuns recModule.layout.entry id recModule (.cons (.value 5) .nil)) :=
  Core.args_isRefinedBy _ _ recModule factFn ⟨trivial, trivial⟩

/-- `@even` on any argument refines itself on a refined one, with memory. -/
theorem even_args {a a' : HVector toType (evenFn.params.map (·.2))}
    (h : a.Forall₂ TyRefinement.IsRefinedBy a') :
    observable (evenFn.memRuns recModule.layout.entry id recModule a) ⊑
      observable (evenFn.memRuns recModule.layout.entry id recModule a') :=
  Core.args_isRefinedBy _ _ recModule evenFn h

/-! # A callee that always hits UB -/

/-- `@count`: `@g` of `%n` at `0`, and otherwise itself on `%n - 1`. -/
def countFn : Func CoreDialect where
  name := "count"
  params := [("n", i 32)]
  results := [i 32]
  body := ⟨none, [
    ⟨"entry", [], [
      op [("zero", i 32)] (.const 32 0) [] 0,
      op [("z", i 1)] (.icmp .eq 32) ["n", "zero"] 0,
      op [] .condBr ["z"] 0 [⟨"base", []⟩, ⟨"rec", []⟩]]⟩,
    ⟨"base", [], [
      op [("b", i 32)] (.call "g" [i 32] [i 32]) ["n"] 0,
      op [] (.ret [i 32]) ["b"] 0]⟩,
    ⟨"rec", [], [
      op [("one", i 32)] (.const 32 1) [] 0,
      op [("m", i 32)] (.sub 32 {}) ["n", "one"] 0,
      op [("r", i 32)] (.call "count" [i 32] [i 32]) ["m"] 0,
      op [] (.ret [i 32]) ["r"] 0]⟩]⟩

/-- `@g`: divides by zero, then calls itself. -/
def gFn : Func CoreDialect where
  name := "g"
  params := [("x", i 32)]
  results := [i 32]
  body := ⟨none, [
    ⟨"entry", [], [
      op [("zero", i 32)] (.const 32 0) [] 0,
      op [("q", i 32)] (.udiv 32 false) ["x", "zero"] 0,
      op [("r", i 32)] (.call "g" [i 32] [i 32]) ["q"] 0,
      op [] (.ret [i 32]) ["r"] 0]⟩]⟩

/-- The module of `@count` and `@g`. -/
def ubModule : Module CoreDialect := ⟨[], [], [.func countFn, .func gFn], [(0, .unknown)]⟩

variable {N : Type} [DecidableEq N] (lay : N → MemLayout)
  (ρ : DialectEffects.Mem CoreDialect → N)

/-- A core op that ends a way in the set monad ends that way with memory,
from any memories, which it keeps. -/
theorem memDenote_of {op : CoreDialect.Op} {args : HVector toType (sig (d := CoreDialect) op)}
    {S : Memory.Memories N (unitsOf lay)} {a : HVector toType (returnTypes (d := CoreDialect) op)}
    (h : DialectDenote.denote (m := SetM) (d := CoreDialect) op args (.ok a)) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
    DialectDenote.denote (m := StateT (Memory.Memories N (unitsOf lay)) SetM) op args S
      (.ok (a, S)) := by
  letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
  rw [((Op.liftsSetM op) lay ρ args).1]
  exact (SetM.lift_apply _ _ _).2 (.inl ⟨a, h, rfl⟩)

/-- A core op that hits UB in the set monad hits it with memory, from any
memories. -/
theorem memDenote_ub {op : CoreDialect.Op} {args : HVector toType (sig (d := CoreDialect) op)}
    {S : Memory.Memories N (unitsOf lay)} {r : String}
    (h : DialectDenote.denote (m := SetM) (d := CoreDialect) op args (.ub r)) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
    DialectDenote.denote (m := StateT (Memory.Memories N (unitsOf lay)) SetM) op args S
      (.ub r) := by
  letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
  rw [((Op.liftsSetM op) lay ρ args).1]
  exact (SetM.lift_apply _ _ _).2 (.inr ⟨r, h, rfl⟩)

/-- `@g` hits UB on every argument with memory, at two steps, wherever a
run names the core's memories. -/
theorem g_ub (a : HVector toType (gFn.params.map (·.2))) :
    ∃ r, (gFn.memRuns lay ρ ubModule a 2).outcomes (.ub r) := by
  letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
  match a with
  | .cons v .nil =>
  have hdiv : ∃ r, DialectDenote.denote (m := SetM) (d := CoreDialect) (.udiv 32 false)
      (.cons v (.cons (.value 0) .nil)) (.ub r) := by
    cases v <;> exact ⟨_, rfl⟩
  obtain ⟨r, hr⟩ := hdiv
  refine ⟨r, (Func.memRuns_ub_iff lay ρ).2 ((Func.memRunsFrom_run (Ev.notStuck_ub r)).2
    ⟨_, Func.enter_ok (f := gFn) rfl rfl (HVector.toDVals_types _), .ub r, ?_, rfl⟩)⟩
  rw [Func.memCall_eq]
  refine (SetM.run_map _ _ _).2 (.inr (.inr ⟨r, ?_, rfl⟩))
  refine (Func.memStepPath_iff (Ev.notStuck_ub r)).2
    (.denote rfl rfl rfl rfl (memDenote_of lay ρ rfl) rfl ?_)
  exact (Func.memStepPath_iff (Ev.notStuck_ub r)).2 (.denoteUB rfl rfl rfl rfl (memDenote_ub lay ρ hr))

/-- `@count` is valid in its module. -/
theorem countFn_valid : countFn.Valid ubModule.context where
  bodyKind := rfl
  entry := ⟨_, rfl, rfl⟩
  reachable b hb := by
    have hentry : countFn.Reachable "entry" := .entry rfl
    simp only [countFn, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hentry
    all_goals exact .step hentry ⟨_, List.mem_cons_self, rfl, by decide⟩
  labelsUnique := by decide
  namesUnique := by decide +kernel
  names x hx := Text.isName_iff.2 (by revert x; decide +kernel)
  labels b hb := Text.isName_iff.2 (by revert b; decide +kernel)
  types t ht := by revert t; decide +kernel
  blocksNonEmpty b hb := by
    simp only [countFn, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp [op]
  ops := opValid_of (dom := []) (fun _ h => nomatch h) (by decide +kernel)
  inner := Func.inner_of_noRegions (by decide +kernel)
  dialect := trivial

/-- `@g` is valid in its module. -/
theorem gFn_valid : gFn.Valid ubModule.context where
  bodyKind := rfl
  entry := ⟨_, rfl, rfl⟩
  reachable b hb := by
    simp only [gFn, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    exact .entry rfl
  labelsUnique := by decide
  namesUnique := by decide +kernel
  names x hx := Text.isName_iff.2 (by revert x; decide +kernel)
  labels b hb := Text.isName_iff.2 (by revert b; decide +kernel)
  types t ht := by revert t; decide +kernel
  blocksNonEmpty b hb := by
    simp only [gFn, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    simp [op]
  ops := opValid_of (dom := []) (fun _ h => nomatch h) (by decide +kernel)
  inner := Func.inner_of_noRegions (by decide +kernel)
  dialect := trivial

/-- The module of `@count` and `@g` is valid. -/
theorem ubModule_valid : ubModule.Valid := Module.valid_of_flat
  (by decide)
  (by decide)
  (⟨by decide, by unfold LocTable.InLimits; decide +kernel, fun e he => by
    simp only [ubModule, List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    simp [Location.WellFormed, Location.refs]⟩)
  (fun f hf => by
    simp only [ubModule, Module.funcs, List.filterMap_cons, Item.func?, List.filterMap_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact countFn_valid
    · exact gFn_valid)
  (by simp [ubModule])
  (by simp [ubModule])

/-- The new body of `@g`: it calls `@count` back on its argument. -/
def gBody : Region CoreDialect := ⟨none, [
    ⟨"entry", [], [
      op [("r", i 32)] (.call "count" [i 32] [i 32]) ["x"] 0,
      op [] (.ret [i 32]) ["r"] 0]⟩]⟩

/-- The module with `@g`'s new body. -/
def ubModule' : Module CoreDialect := ubModule.replaceBody gFn.name gBody

/-- Its functions: `@count`, and `@g` with its new body. -/
theorem ubModule'_funcs : ubModule'.funcs = [countFn, { gFn with body := gBody }] := by
  rw [ubModule', Module.funcs_replaceBody]
  simp [ubModule, Module.funcs, Func.replaceBody, countFn, gFn]

/-- `@g` with its new body is valid in the module's context. -/
theorem gFn'_valid : ({ gFn with body := gBody } : Func CoreDialect).Valid ubModule.context where
  bodyKind := rfl
  entry := ⟨_, rfl, rfl⟩
  reachable b hb := by
    simp only [gBody, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    exact .entry rfl
  labelsUnique := by decide
  namesUnique := by decide +kernel
  names x hx := Text.isName_iff.2 (by revert x; decide +kernel)
  labels b hb := Text.isName_iff.2 (by revert b; decide +kernel)
  types t ht := by revert t; decide +kernel
  blocksNonEmpty b hb := by
    simp only [gBody, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    simp [op]
  ops := opValid_of (dom := []) (fun _ h => nomatch h) (by decide +kernel)
  inner := Func.inner_of_noRegions (by decide +kernel)
  dialect := trivial

/-- The module with `@g`'s new body is valid too. -/
theorem ubModule'_valid : ubModule'.Valid :=
  Module.valid_replaceBody ubModule_valid
    (fun g hg hs => by
      simp only [ubModule, Module.funcs, List.filterMap_cons, Item.func?, List.filterMap_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact absurd hs (by decide)
      · exact gFn'_valid)
    (fun g hg hs => by
      simp only [ubModule, Module.funcs, List.filterMap_cons, Item.func?, List.filterMap_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact absurd hs (by decide)
      · decide +kernel)

-- The validation check accepts both modules. `@count` hits UB, in `@g`,
-- and with `@g`'s new body it calls itself back without end.
#guard ubModule.problems.isEmpty && ubModule'.problems.isEmpty
#guard runValid ubModule.print "@count" ["3"] == ubFor "udiv by zero"
#guard runValid ubModule'.print "@count" ["3"] (fuel := 1000) == exhausted

/-- Every call of `ubModule` names one of its functions, so no summary of
it touches memory. -/
theorem ubModule_noMemory (s : Name) : (ubModule.table.summary s).TouchesNoMemory :=
  Core.summary_touchesNoMemory (by decide +kernel) s

/-- Every call of the module with `@g`'s new body names one of its functions
too. -/
theorem ubModule'_noMemory (s : Name) : (ubModule'.table.summary s).TouchesNoMemory :=
  Core.summary_touchesNoMemory (by decide +kernel) s

/-- `@g` with its new body refines `@g` with memory: `@g` hits UB on every
argument. -/
theorem g_isRefinedBy :
    gFn.memRuns lay ρ ubModule ⊑ (gFn.replaceBody gFn.name gBody).memRuns lay ρ ubModule' :=
  fun a =>
    let ⟨_, h⟩ := g_ub lay ρ a
    Behaviour.ub_isRefinedBy ⟨2, h⟩ _

/-- So `@count`, which calls `@g` and itself, is refined with memory by
itself in the module with `@g`'s new body, which calls `@count` back. -/
theorem count_isRefinedBy : countFn.memRuns lay ρ ubModule ⊑ countFn.memRuns lay ρ ubModule' :=
  Core.caller_isRefinedBy lay ρ ubModule_valid (by simp [ubModule, Module.funcs])
    (by simp [gFn, Core.Ty.Finite]) gBody (ubModule_noMemory _) (ubModule'_noMemory _)
    (g_isRefinedBy lay ρ) (by simp [ubModule, Module.funcs]) (by decide)

/-- Every function of the module is refined with memory by its counterpart
with `@g`'s new body. -/
theorem ubModule_isRefinedBy {f : Func CoreDialect} (hf : f ∈ ubModule.funcs) :
    f.memRuns lay ρ ubModule ⊑ (f.replaceBody gFn.name gBody).memRuns lay ρ ubModule' :=
  Core.replaceBody_isRefinedBy lay ρ ubModule_valid (by simp [ubModule, Module.funcs])
    (by simp [gFn, Core.Ty.Finite]) gBody (ubModule_noMemory _) (ubModule'_noMemory _)
    (g_isRefinedBy lay ρ) hf

/-! # A callee replaced by itself, in mutual recursion -/

/-- Replacing `@odd`'s body with itself leaves the module as it was. -/
theorem recModule_replace_odd : recModule.replaceBody oddFn.name oddFn.body = recModule := by
  simp [Module.replaceBody, Item.replaceBody, recModule, Func.replaceBody, factFn, evenFn, oddFn,
    parityFn]

/-- Every call of `recModule` names one of its functions, so no summary of
it touches memory. -/
theorem recModule_noMemory (s : Name) : (recModule.table.summary s).TouchesNoMemory :=
  Core.summary_touchesNoMemory (by decide +kernel) s

/-- `@odd` with its own body refines `@odd` with memory. -/
theorem odd_self_isRefinedBy :
    oddFn.memRuns lay ρ recModule ⊑
      (oddFn.replaceBody oddFn.name oddFn.body).memRuns lay ρ
        (recModule.replaceBody oddFn.name oddFn.body) := by
  rw [recModule_replace_odd]
  show oddFn.memRuns lay ρ recModule ⊑
    Func.memRuns lay ρ recModule
      { oddFn with body := if oddFn.name = oddFn.name then oddFn.body else oddFn.body }
  rw [ite_self]
  exact Core.funcRuns_isRefinedBy_refl _

/-- So `@even`, which calls `@odd`, which calls it back, is refined with
memory by itself. -/
theorem even_replace_isRefinedBy :
    evenFn.memRuns lay ρ recModule ⊑
      evenFn.memRuns lay ρ (recModule.replaceBody oddFn.name oddFn.body) :=
  Core.caller_isRefinedBy lay ρ recModule_valid (by simp [recModule, Module.funcs])
    (by simp [oddFn, parityFn, Core.Ty.Finite]) oddFn.body (recModule_noMemory _)
    (by rw [recModule_replace_odd]; exact recModule_noMemory _) (odd_self_isRefinedBy lay ρ)
    (by simp [recModule, Module.funcs]) (by decide)

/-! # Axioms

The steps of a run, the engine and its two inductions, the general
theorems, their core instances and the tests above. -/

/-- info: 'Fir.Func.stepPath_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.stepPath_iff

/-- info: 'Fir.Func.runOps_exhausted_down' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.runOps_exhausted_down

/-- info: 'Fir.Env.IsRefinedBy.operands' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Env.IsRefinedBy.operands

/-- info: 'Fir.Func.enter_isRefinedBy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.enter_isRefinedBy

/-- info: 'Fir.Env.IsRefinedBy.jump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Env.IsRefinedBy.jump

/-- info: 'Fir.Func.call_cont' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.call_cont

/-- info: 'Fir.BlackBox.allowed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.BlackBox.allowed

/-- info: 'Fir.Func.runOps_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.runOps_allowed

/-- info: 'Fir.BlackBox.allowedBelow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.BlackBox.allowedBelow

/-- info: 'Fir.Func.runOps_allowedBelow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.runOps_allowedBelow

/-- info: 'Fir.Func.runs_isRefinedBy_of_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.runs_isRefinedBy_of_calls

/-- info: 'Fir.Func.runs_args_isRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.runs_args_isRefinedBy

/-- info: 'Fir.Func.runs_exhausted_down' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.runs_exhausted_down

/-- info: 'Fir.exists_common_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.exists_common_bound

/-- info: 'Fir.Module.valid_replaceBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Module.valid_replaceBody

/-- info: 'Fir.Func.runs_replaceBody_isRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.runs_replaceBody_isRefinedBy

/-- info: 'Fir.Func.memRunsFrom_isRefinedBy_of_memRuns' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.memRunsFrom_isRefinedBy_of_memRuns

/-- info: 'Fir.Func.memRuns_replaceBody_isRefinedBy_of_memRuns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.memRuns_replaceBody_isRefinedBy_of_memRuns

/-- info: 'Fir.Core.Op.monotone_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.Op.monotone_all

/-- info: 'Fir.Core.args_isRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.args_isRefinedBy

/-- info: 'Fir.Core.replaceBody_isRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.replaceBody_isRefinedBy

/-- info: 'Fir.Core.caller_isRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.caller_isRefinedBy

/-- info: 'FirTest.fact_args' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.fact_args

/-- info: 'FirTest.even_args' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.even_args

/-- info: 'FirTest.g_ub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.g_ub

/-- info: 'FirTest.ubModule'_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.ubModule'_valid

/-- info: 'FirTest.g_isRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.g_isRefinedBy

/-- info: 'FirTest.count_isRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.count_isRefinedBy

/-- info: 'FirTest.ubModule_isRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.ubModule_isRefinedBy

/-- info: 'FirTest.even_replace_isRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.even_replace_isRefinedBy

end FirTest
