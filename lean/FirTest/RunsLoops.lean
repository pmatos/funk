import FirTest.ValidSum
import FirTest.Run

/-!
Tests of progress and no stuck path for core functions with jumps and
loops: the theorems applied to valid functions, which shows that their
hypotheses can be met, and the axioms of their proofs.

`@sum`, the spec's example, loops until its counter reaches its argument.
`@forever` passes a block argument round a loop that never ends, so every
run of it runs out of fuel: progress holds because running out of fuel is
an outcome. `@sum10` calls `@sum`, so it is not `CallFree`: the theorems
for every valid core function cover it, which `FirTest.RunsCalls` applies.
-/

namespace FirTest

open Fir Core Example

/-! # `@sum` -/

#guard decide (CallFree sum) && !decide (CallFree sum10)

/-- `@sum` is a function of its module. -/
theorem sum_mem : sum ∈ sumModule.funcs := by
  simp [sumModule, Module.funcs]

/-- More fuel never changes how a run of `@sum` returns or hits UB. -/
theorem sum_fuelMonotone (args : HVector toType (sum.params.map (·.2))) :
    FuelMonotone (funcRuns sumModule sum args) :=
  callFree_fuelMonotone sumModule_valid sum_mem (by decide) args

/-- A run of `@sum` has an outcome at every budget. -/
theorem sum_progress (args : HVector toType (sum.params.map (·.2))) :
    Progress (funcRuns sumModule sum args) :=
  callFree_progress sumModule_valid sum_mem (by decide) args

/-- No path of a run of `@sum` is stuck. -/
theorem sum_neverStuck (args : HVector toType (sum.params.map (·.2))) :
    NeverStuck (funcRuns sumModule sum args) :=
  callFree_neverStuck sumModule_valid sum_mem (by decide) args

/-! # A loop that never ends -/

/-- `@forever` adds one to a block argument on every trip round `^loop`, and
never leaves it. -/
def forever : Func CoreDialect where
  name := "forever"
  params := [("x", i 8)]
  results := [i 8]
  body := ⟨none, [
    ⟨"entry", [], [
      op [] .br [] 0 [⟨"loop", ["x"]⟩]]⟩,
    ⟨"loop", [("a", i 8)], [
      op [("one", i 8)] (.const 8 1) [] 0,
      op [("b", i 8)] (.add 8 {}) ["a", "one"] 0,
      op [] .br [] 0 [⟨"loop", ["b"]⟩]]⟩]⟩

/-- A module that holds `@forever`. -/
def foreverModule : Module CoreDialect := ⟨[], [.func forever], [(0, .unknown)]⟩

#guard foreverModule.problems.isEmpty
#guard foreverModule.print == "\n".intercalate [
  "func @forever(%x: i8) -> i8 {",
  "^entry:",
  "  br ^loop(%x) @0",
  "^loop(%a: i8):",
  "  %one: i8 = const 1 @0",
  "  %b: i8 = add %a, %one @0",
  "  br ^loop(%b) @0",
  "}",
  "",
  "locs {",
  "  @0 = unknown",
  "}",
  ""]

-- `fir-ref run` runs out of fuel on `@forever` at every budget.
#guard [0, 1, 4, 1000].all fun n =>
  runText foreverModule.print "@forever" ["5"] (fuel := n) == exhausted

/-- `@forever` is valid in its module. Every use is of a parameter or of an
argument or earlier result of its own block. -/
theorem forever_valid : forever.Valid foreverModule.context where
  bodyKind := rfl
  entry := ⟨_, rfl, rfl⟩
  reachable b hb := by
    have hentry : forever.Reachable "entry" := .entry rfl
    simp only [forever, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hentry
    · exact .step hentry ⟨_, List.mem_cons_self, rfl, by decide⟩
  labelsUnique := by decide
  namesUnique := by decide +kernel
  names x hx := Text.isName_iff.2 (by revert x; decide +kernel)
  labels b hb := Text.isName_iff.2 (by revert b; decide +kernel)
  types t ht := by revert t; decide +kernel
  blocksNonEmpty b hb := by
    simp only [forever, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> simp [op]
  ops := opValid_of (dom := []) (fun _ h => nomatch h) (by decide +kernel)
  dialect := trivial

/-- `@forever`'s module is valid. -/
theorem foreverModule_valid : foreverModule.Valid := Module.valid_of_flat
  (by decide)
  (by decide)
  (⟨by decide, by unfold LocTable.InLimits; decide +kernel, fun e he => by
    simp only [foreverModule, List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    simp [Location.WellFormed, Location.refs]⟩)
  (fun f hf => by
    simp only [foreverModule, Module.funcs, List.filterMap_cons, Item.func?, List.filterMap_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hf
    subst hf
    exact forever_valid)
  (by simp [foreverModule])
  (by simp [foreverModule])

/-- `@forever` is a function of its module. -/
theorem forever_mem : forever ∈ foreverModule.funcs := by
  simp [foreverModule, Module.funcs]

/-- Every run of `@forever` has an outcome, no path of it is stuck, and more
fuel never changes how it returns or hits UB, which it never does. -/
theorem forever_runsWell (args : HVector toType (forever.params.map (·.2))) :
    RunsWell (funcRuns foreverModule forever args) :=
  ⟨callFree_fuelMonotone foreverModule_valid forever_mem (by decide) args,
    callFree_progress foreverModule_valid forever_mem (by decide) args,
    callFree_neverStuck foreverModule_valid forever_mem (by decide) args⟩

/-! # Axioms

The general theorems hold for every valid local function, and the core
theorems for every valid core function without calls. -/

/-- info: 'Fir.Func.neverStuck_of_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.neverStuck_of_local

/-- info: 'Fir.Func.progress_of_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.progress_of_local

/-- info: 'Fir.Core.local_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.local_of_valid

/-- info: 'Fir.Core.callFree_runsWell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.callFree_runsWell

/-- info: 'Fir.Core.callFree_fuelMonotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.callFree_fuelMonotone

/-- info: 'Fir.Core.callFree_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.callFree_progress

/-- info: 'Fir.Core.callFree_neverStuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.callFree_neverStuck

/-- info: 'FirTest.sum_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.sum_progress

/-- info: 'FirTest.sum_neverStuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.sum_neverStuck

/-- info: 'FirTest.forever_runsWell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.forever_runsWell

end FirTest
