import Fir.Core.CallRefine
import FirTest.RunsCalls

/-!
Tests of #20's two function-level refinement theorems, applied to valid
modules with calls and recursion, which shows that their hypotheses can
be met, and the axioms of their proofs.

* Refined arguments, with memory: `@fact`, which calls itself, on a poison
  argument is refined by `@fact` on `5`; and `@even`, which calls `@odd`,
  which calls it back, on any arguments is refined by itself on refined
  ones.
* Congruence in the callee: `@g` divides by zero before it calls itself,
  so it hits UB on every argument, and every body refines it. `@count`
  calls `@g` and itself. With a new body for `@g`, which calls `@count`
  back, the module is still valid, and each of its functions is refined
  by its counterpart: `@count` hits UB in the old module and runs out of
  fuel in the new. A second instance gives `@odd` its own body, in the
  mutual recursion of `@even` and `@odd`.
* Congruence in the callee, with memory: `@g` given a body with no blocks
  meets its hypotheses, so `@count` is refined with memory by itself.
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

/-- `@g` hits UB on every argument, at two steps. -/
theorem g_ub (a : HVector toType (gFn.params.map (·.2))) :
    ∃ r, (funcRuns ubModule gFn a 2).outcomes (.ub r) := by
  match a with
  | .cons v .nil =>
  have hne : ∀ r : String,
      Ev.NotStuck (.ub r : Ev (Except Stuck (Result (List (DVal CoreDialect) × Nat)))) :=
    fun _ _ h => nomatch h
  have hdiv : ∃ r, DialectDenote.denote (m := SetM) (d := CoreDialect) (.udiv 32 false)
      (.cons v (.cons (.value 0) .nil)) (.ub r) := by
    cases v <;> exact ⟨_, rfl⟩
  obtain ⟨r, hr⟩ := hdiv
  refine ⟨r, Func.runs_of_runOps (M := ubModule) (g := gFn) (a := .cons v .nil) (N := 2)
    (Func.enter_ok (f := gFn) rfl rfl (HVector.toDVals_types _)) (e := .ub r) ?_⟩
  refine (Func.stepPath_iff (hne r)).2 (.denote rfl rfl rfl rfl rfl rfl ?_)
  exact (Func.stepPath_iff (hne r)).2 (.denoteUB rfl rfl rfl rfl hr)

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

/-- `@g` with its new body refines `@g`: `@g` hits UB on every argument. -/
theorem g_isRefinedBy :
    funcRuns ubModule gFn ⊑ funcRuns ubModule' (gFn.replaceBody gFn.name gBody) := fun a =>
  let ⟨_, h⟩ := g_ub a
  Behaviour.ub_isRefinedBy ⟨2, h⟩ _

/-- So `@count`, which calls `@g` and itself, is refined by itself in the
module with `@g`'s new body, which calls `@count` back. -/
theorem count_isRefinedBy : funcRuns ubModule countFn ⊑ funcRuns ubModule' countFn :=
  Core.caller_isRefinedBy ubModule_valid (by simp [ubModule, Module.funcs])
    (by simp [gFn, Core.Ty.Finite]) gBody g_isRefinedBy (by simp [ubModule, Module.funcs])
    (by decide)

/-- Every function of the module is refined by its counterpart with
`@g`'s new body. -/
theorem ubModule_isRefinedBy {f : Func CoreDialect} (hf : f ∈ ubModule.funcs) :
    funcRuns ubModule f ⊑ funcRuns ubModule' (f.replaceBody gFn.name gBody) :=
  Core.replaceBody_isRefinedBy ubModule_valid (by simp [ubModule, Module.funcs])
    (by simp [gFn, Core.Ty.Finite]) gBody g_isRefinedBy hf

/-! # A callee replaced by itself, in mutual recursion -/

/-- `@odd` with its own body refines `@odd`. -/
theorem odd_self_isRefinedBy :
    funcRuns recModule oddFn ⊑
      funcRuns (recModule.replaceBody oddFn.name oddFn.body)
        (oddFn.replaceBody oddFn.name oddFn.body) := by
  have hM : recModule.replaceBody oddFn.name oddFn.body = recModule := by
    simp [Module.replaceBody, Item.replaceBody, recModule, Func.replaceBody, factFn, evenFn, oddFn,
      parityFn]
  rw [hM]
  show funcRuns recModule oddFn ⊑
    funcRuns recModule
      { oddFn with body := if oddFn.name = oddFn.name then oddFn.body else oddFn.body }
  rw [ite_self]
  exact Core.funcRuns_isRefinedBy_refl _

/-- So `@even`, which calls `@odd`, which calls it back, is refined by
itself. -/
theorem even_replace_isRefinedBy :
    funcRuns recModule evenFn ⊑ funcRuns (recModule.replaceBody oddFn.name oddFn.body) evenFn :=
  Core.caller_isRefinedBy recModule_valid (by simp [recModule, Module.funcs])
    (by simp [oddFn, parityFn, Core.Ty.Finite]) oddFn.body odd_self_isRefinedBy
    (by simp [recModule, Module.funcs]) (by decide)

/-! # Congruence in the callee, with memory

With memory, congruence asks that the new `@g` refine the old from every
memories, and that its runs be bounded. A body with no blocks meets both:
`@g` with it never starts, so it has no behaviour, and no run of it runs out
of fuel. So `@count` is refined with memory by itself in the module with
that body. -/

/-- A body with no blocks: a function with it never starts. -/
def noBlocks : Region CoreDialect := { blocks := [] }

/-- The memories of a run of `ubModule`, at its layout. -/
abbrev UbMems := Memory.Memories Nat (unitsOf ubModule.layout.entry)

/-- `@g` with no blocks, in its module so changed, has no outcome from any
memories: each path is stuck. -/
theorem noBlocks_outcomes (a : HVector toType (gFn.params.map (·.2))) (S : UbMems) (m : Nat)
    (o : Outcome (List (DVal CoreDialect) × UbMems)) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) ubModule.layout.entry id
    ¬ ((gFn.replaceBody gFn.name noBlocks).memRunsFrom (ubModule.replaceBody gFn.name noBlocks)
      (a, S) m).outcomes o := by
  letI := DialectMemDenote.denoteAt (d := CoreDialect) ubModule.layout.entry id
  have key : ∀ x, Ev.NotStuck x → ¬ ((gFn.replaceBody gFn.name noBlocks).memRunsFrom
      (ubModule.replaceBody gFn.name noBlocks) (a, S) m) x := by
    intro x hx h
    obtain ⟨p, hp, -⟩ := (Func.memRunsFrom_run hx).1 h
    simp [Func.enter, Func.blocks, noBlocks, stuck] at hp
  cases o with
  | ret _ => exact key _ fun _ h => nomatch h
  | ub _ => exact key _ fun _ h => nomatch h
  | fuelExhausted => exact key _ fun _ h => nomatch h

/-- `@count` is refined with memory by itself in the module where `@g` has
no blocks. -/
theorem count_memIsRefinedBy :
    countFn.memRuns ubModule.layout.entry id ubModule ⊑
      countFn.memRuns ubModule.layout.entry id (ubModule.replaceBody gFn.name noBlocks) := by
  letI := DialectMemDenote.denoteAt (d := CoreDialect) ubModule.layout.entry id
  refine Core.memCaller_isRefinedBy _ _ ubModule_valid (by simp [ubModule, Module.funcs])
    noBlocks ⟨0, fun ⟨a, S⟩ => .inr fun m _ => noBlocks_outcomes a S m .fuelExhausted⟩ ?_
    (by simp [ubModule, Module.funcs]) (by decide)
  intro ⟨a, S⟩ t ht
  cases t with
  | ret o => obtain ⟨n, hn⟩ := ht; exact (noBlocks_outcomes a S n (.ret o) hn).elim
  | ub r => obtain ⟨n, hn⟩ := ht; exact (noBlocks_outcomes a S n (.ub r) hn).elim
  | fuelExhausted => exact (noBlocks_outcomes a S 0 .fuelExhausted (ht 0)).elim

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

/-- info: 'Fir.Core.Op.monotone_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.Op.monotone_all

/-- info: 'Fir.Core.args_isRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.args_isRefinedBy

/-- info: 'Fir.Core.replaceBody_isRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.replaceBody_isRefinedBy

/-- info: 'Fir.Core.caller_isRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.caller_isRefinedBy

/-- info: 'Fir.Core.memReplaceBody_isRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.memReplaceBody_isRefinedBy

/-- info: 'FirTest.count_memIsRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.count_memIsRefinedBy

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
