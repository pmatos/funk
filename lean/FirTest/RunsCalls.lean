import FirTest.RunsLoops
import FirTest.Calls

/-!
Tests of progress and no stuck path for core functions with calls and
recursion: the theorems applied to valid modules whose functions call
each other and themselves, which shows that their hypotheses can be met,
and the axioms of their proofs.

`@sum10`, of the spec's example module, calls `@sum`. `@fact` calls
itself, and `@even` and `@odd` call each other: the module of the three
is the abstract syntax of the texts that `FirTest.Calls` runs. None of
these functions is `CallFree`, so the theorems for functions without
calls say nothing of them.
-/

namespace FirTest

open Fir Core Example

/-! # `@sum10` -/

/-- `@sum10` is a function of its module. -/
theorem sum10_mem : sum10 ∈ sumModule.funcs := by
  simp [sumModule, Module.funcs]

/-- Every run of `@sum10`, which calls `@sum`, has an outcome, no path of
it is stuck, and more fuel never changes how it returns or hits UB. -/
theorem sum10_runsWell (args : HVector toType (sum10.params.map (·.2))) :
    RunsWell (funcRuns sumModule sum10 args) :=
  Core.runsWell sumModule_valid sum10_mem args

/-! # Recursion and mutual recursion -/

/-- `@fact`, the factorial at `i64`, which calls itself. -/
def factFn : Func CoreDialect where
  name := "fact"
  params := [("n", i 64)]
  results := [i 64]
  body := ⟨[
    ⟨"entry", [], [
      op [("one", i 64)] (.const 64 1) [] 0,
      op [("small", i 1)] (.icmp .sle 64) ["n", "one"] 0,
      op [] .condBr ["small"] 0 [⟨"base", []⟩, ⟨"rec", []⟩]]⟩,
    ⟨"base", [], [
      op [("c", i 64)] (.const 64 1) [] 0,
      op [] (.ret [i 64]) ["c"] 0]⟩,
    ⟨"rec", [], [
      op [("one1", i 64)] (.const 64 1) [] 0,
      op [("m", i 64)] (.sub 64 {}) ["n", "one1"] 0,
      op [("r", i 64)] (.call "fact" [i 64] [i 64]) ["m"] 0,
      op [("p", i 64)] (.mul 64 {}) ["n", "r"] 0,
      op [] (.ret [i 64]) ["p"] 0]⟩]⟩

/-- `@even` or `@odd`, as `name`: `base` at `0`, and otherwise what `other`
gives on `%n - 1`. -/
def parityFn (name other : String) (base : BitVec 1) : Func CoreDialect where
  name := name
  params := [("n", i 32)]
  results := [i 1]
  body := ⟨[
    ⟨"entry", [], [
      op [("zero", i 32)] (.const 32 0) [] 0,
      op [("z", i 1)] (.icmp .eq 32) ["n", "zero"] 0,
      op [] .condBr ["z"] 0 [⟨"yes", []⟩, ⟨"no", []⟩]]⟩,
    ⟨"yes", [], [
      op [("b", i 1)] (.const 1 base) [] 0,
      op [] (.ret [i 1]) ["b"] 0]⟩,
    ⟨"no", [], [
      op [("one", i 32)] (.const 32 1) [] 0,
      op [("m", i 32)] (.sub 32 {}) ["n", "one"] 0,
      op [("r", i 1)] (.call other [i 32] [i 1]) ["m"] 0,
      op [] (.ret [i 1]) ["r"] 0]⟩]⟩

/-- `@even`, which calls `@odd`. -/
def evenFn : Func CoreDialect := parityFn "even" "odd" 1

/-- `@odd`, which calls `@even`. -/
def oddFn : Func CoreDialect := parityFn "odd" "even" 0

/-- The module of `@fact`, `@even` and `@odd`. -/
def recModule : Module CoreDialect := ⟨[.func factFn, .func evenFn, .func oddFn], [(0, .unknown)]⟩

-- It is the module of the texts that `FirTest.Calls` runs, and the
-- validation check accepts it.
#guard recModule.print ==
  withFuncs [factSource, parity "even" "odd" "true", parity "odd" "even" "false"]
#guard recModule.problems.isEmpty
#guard !decide (CallFree factFn) && !decide (CallFree evenFn) && !decide (CallFree oddFn)
#guard runText recModule.print "@fact" ["5"] == returns ["120"] &&
  runText recModule.print "@odd" ["7"] == returns ["true"]

/-- `@fact` is valid in its module: every use is of its parameter or of an
earlier result of its own block, and its `call` names `@fact` at its
type. -/
theorem factFn_valid : factFn.Valid recModule.context where
  entry := ⟨_, rfl, rfl⟩
  reachable b hb := by
    have hentry : factFn.Reachable "entry" := .entry rfl
    simp only [factFn, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hentry
    all_goals exact .step hentry ⟨_, List.mem_cons_self, rfl, by decide⟩
  labelsUnique := by decide
  namesUnique := by decide +kernel
  names x hx := Text.isName_iff.2 (by revert x; decide +kernel)
  labels b hb := Text.isName_iff.2 (by revert b; decide +kernel)
  types t ht := by revert t; decide +kernel
  blocksNonEmpty b hb := by
    simp only [factFn, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp [op]
  ops := opValid_of (dom := []) (fun _ h => nomatch h) (by decide +kernel)

/-- `@even` is valid in its module: its `call` names `@odd` at its type. -/
theorem evenFn_valid : evenFn.Valid recModule.context where
  entry := ⟨_, rfl, rfl⟩
  reachable b hb := by
    have hentry : evenFn.Reachable "entry" := .entry rfl
    simp only [evenFn, parityFn, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hentry
    all_goals exact .step hentry ⟨_, List.mem_cons_self, rfl, by decide⟩
  labelsUnique := by decide
  namesUnique := by decide +kernel
  names x hx := Text.isName_iff.2 (by revert x; decide +kernel)
  labels b hb := Text.isName_iff.2 (by revert b; decide +kernel)
  types t ht := by revert t; decide +kernel
  blocksNonEmpty b hb := by
    simp only [evenFn, parityFn, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp [op]
  ops := opValid_of (dom := []) (fun _ h => nomatch h) (by decide +kernel)

/-- `@odd` is valid in its module: its `call` names `@even` at its type. -/
theorem oddFn_valid : oddFn.Valid recModule.context where
  entry := ⟨_, rfl, rfl⟩
  reachable b hb := by
    have hentry : oddFn.Reachable "entry" := .entry rfl
    simp only [oddFn, parityFn, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hentry
    all_goals exact .step hentry ⟨_, List.mem_cons_self, rfl, by decide⟩
  labelsUnique := by decide
  namesUnique := by decide +kernel
  names x hx := Text.isName_iff.2 (by revert x; decide +kernel)
  labels b hb := Text.isName_iff.2 (by revert b; decide +kernel)
  types t ht := by revert t; decide +kernel
  blocksNonEmpty b hb := by
    simp only [oddFn, parityFn, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp [op]
  ops := opValid_of (dom := []) (fun _ h => nomatch h) (by decide +kernel)

/-- The module of `@fact`, `@even` and `@odd` is valid. -/
theorem recModule_valid : recModule.Valid where
  symbolsUnique := by decide
  locs := ⟨by decide, by unfold LocTable.InLimits; decide +kernel, fun e he => by
    simp only [recModule, List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    simp [Location.WellFormed, Location.refs]⟩
  funcs f hf := by
    simp only [recModule, Module.funcs, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact factFn_valid
    · exact evenFn_valid
    · exact oddFn_valid

/-- Every run of `@fact`, which calls itself, has an outcome, no path of
it is stuck, and more fuel never changes how it returns or hits UB. -/
theorem fact_runsWell (args : HVector toType (factFn.params.map (·.2))) :
    RunsWell (funcRuns recModule factFn args) :=
  Core.runsWell recModule_valid (by simp [recModule, Module.funcs]) args

/-- A run of `@even`, which calls `@odd`, which calls it back, has an
outcome at every budget. -/
theorem even_progress (args : HVector toType (evenFn.params.map (·.2))) :
    Progress (funcRuns recModule evenFn args) :=
  Core.progress recModule_valid (by simp [recModule, Module.funcs]) args

/-- No path of a run of `@odd`, which calls `@even`, which calls it back,
is stuck. -/
theorem odd_neverStuck (args : HVector toType (oddFn.params.map (·.2))) :
    NeverStuck (funcRuns recModule oddFn args) :=
  Core.neverStuck recModule_valid (by simp [recModule, Module.funcs]) args

/-- More fuel never changes how a run of `@odd` returns or hits UB. -/
theorem odd_fuelMonotone (args : HVector toType (oddFn.params.map (·.2))) :
    FuelMonotone (funcRuns recModule oddFn args) :=
  Core.fuelMonotone recModule_valid (by simp [recModule, Module.funcs]) args

/-! # Axioms

The general theorems hold for every function of a module whose functions
are valid and run within it, and the core theorems for every function of
every valid core module. -/

/-- info: 'Fir.Func.runOps_returns' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.runOps_returns

/-- info: 'Fir.Module.calls_noStuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Module.calls_noStuck

/-- info: 'Fir.Module.calls_hasPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Module.calls_hasPath

/-- info: 'Fir.Func.neverStuck_of_inModule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.neverStuck_of_inModule

/-- info: 'Fir.Func.progress_of_inModule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.progress_of_inModule

/-- info: 'Fir.Core.call_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.call_total

/-- info: 'Fir.Core.call_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.call_monotone

/-- info: 'Fir.Core.Op.total_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.Op.total_all

/-- info: 'Fir.Core.inModule_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.inModule_of_valid

/-- info: 'Fir.Core.runsWell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.runsWell

/-- info: 'Fir.Core.fuelMonotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.fuelMonotone

/-- info: 'Fir.Core.progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.progress

/-- info: 'Fir.Core.neverStuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.neverStuck

/-- info: 'FirTest.sum10_runsWell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.sum10_runsWell

/-- info: 'FirTest.fact_runsWell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.fact_runsWell

/-- info: 'FirTest.even_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.even_progress

/-- info: 'FirTest.odd_neverStuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.odd_neverStuck

end FirTest
