import FirTest.RefineCallsFrom

/-!
Tests of congruence in the callee with memory for a callee with a pointer
parameter, which has infinitely many argument vectors: `@pid` returns the
pointer it is given, and `@pcall` calls it. Replacing the body of `@pid`
with its own body refines `@pcall` with memory, with no budget, by the
theorem from given memories (#214).
-/

namespace FirTest

open Fir Core

/-- `@pid`, which returns the pointer it is given. -/
def pidFn : Func CoreDialect where
  name := "pid"
  params := [("p", .ptr 0)]
  results := [.ptr 0]
  body := ⟨none, [⟨"entry", [], [op [] (.ret [.ptr 0]) ["p"] 0]⟩]⟩

/-- `@pcall`, which calls `@pid` on its pointer. -/
def pcallFn : Func CoreDialect where
  name := "pcall"
  params := [("p", .ptr 0)]
  results := [.ptr 0]
  body := ⟨none, [⟨"entry", [], [
    op [("r", .ptr 0)] (.call "pid" [.ptr 0] [.ptr 0]) ["p"] 0,
    op [] (.ret [.ptr 0]) ["r"] 0]⟩]⟩

/-- The module of `@pid` and `@pcall`. -/
def ptrModule : Module CoreDialect := ⟨[], [], [.func pidFn, .func pcallFn], [(0, .unknown)]⟩

#guard ptrModule.problems.isEmpty

/-- `@pid` is valid in its module. -/
theorem pidFn_valid : pidFn.Valid ptrModule.context where
  bodyKind := rfl
  entry := ⟨_, rfl, rfl⟩
  reachable b hb := by
    simp only [pidFn, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    exact .entry rfl
  labelsUnique := by decide
  namesUnique := by decide +kernel
  names x hx := Text.isName_iff.2 (by revert x; decide +kernel)
  labels b hb := Text.isName_iff.2 (by revert b; decide +kernel)
  types t ht := by revert t; decide +kernel
  blocksNonEmpty b hb := by
    simp only [pidFn, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    simp [op]
  ops := opValid_of (dom := []) (fun _ h => nomatch h) (by decide +kernel)
  inner := Func.inner_of_noRegions (by decide +kernel)
  dialect := trivial

/-- `@pcall` is valid in its module: its `call` names `@pid` at its type. -/
theorem pcallFn_valid : pcallFn.Valid ptrModule.context where
  bodyKind := rfl
  entry := ⟨_, rfl, rfl⟩
  reachable b hb := by
    simp only [pcallFn, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    exact .entry rfl
  labelsUnique := by decide
  namesUnique := by decide +kernel
  names x hx := Text.isName_iff.2 (by revert x; decide +kernel)
  labels b hb := Text.isName_iff.2 (by revert b; decide +kernel)
  types t ht := by revert t; decide +kernel
  blocksNonEmpty b hb := by
    simp only [pcallFn, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    simp [op]
  ops := opValid_of (dom := []) (fun _ h => nomatch h) (by decide +kernel)
  inner := Func.inner_of_noRegions (by decide +kernel)
  dialect := trivial

/-- The module of `@pid` and `@pcall` is valid. -/
theorem ptrModule_valid : ptrModule.Valid := Module.valid_of_flat
  (by decide)
  (by decide)
  (⟨by decide, by unfold LocTable.InLimits; decide +kernel, fun e he => by
    simp only [ptrModule, List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    simp [Location.WellFormed, Location.refs]⟩)
  (fun f hf => by
    simp only [ptrModule, Module.funcs, List.filterMap_cons, Item.func?, List.filterMap_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact pidFn_valid
    · exact pcallFn_valid)
  (by simp [ptrModule])
  (by simp [ptrModule])

/-- `@pid` has a pointer parameter, so its argument vectors are infinitely
many: the forms of congruence that ask for finitely many do not cover it. -/
theorem pidFn_not_finite : ¬ ∀ t ∈ pidFn.params.map (·.2), t.Finite := by
  simp [pidFn, Core.Ty.Finite]

/-- The module with `@pid`'s own body is the module. -/
theorem ptrModule_replace_pid : ptrModule.replaceBody pidFn.name pidFn.body = ptrModule := by
  simp [Module.replaceBody, Item.replaceBody, ptrModule, Func.replaceBody, pidFn, pcallFn]

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem CoreDialect → N)

/-- `@pid` with its own body refines `@pid` from given memories. -/
theorem pid_self_isRefinedBy :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
    pidFn.memRunsFrom (Mem := N) (unit := unitsOf lay) ptrModule ⊑
      (pidFn.replaceBody pidFn.name pidFn.body).memRunsFrom (Mem := N) (unit := unitsOf lay)
        (ptrModule.replaceBody pidFn.name pidFn.body) := by
  letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
  rw [ptrModule_replace_pid]
  show pidFn.memRunsFrom ptrModule ⊑ Func.memRunsFrom ptrModule
    { pidFn with body := if pidFn.name = pidFn.name then pidFn.body else pidFn.body }
  rw [ite_self]
  have hm : ∀ g : Func CoreDialect, g.MemOpsMonotone N (unitsOf lay) :=
    fun _ _ _ o _ hc => Op.memMonotone_all o.op hc lay ρ
  exact fun p => Func.memRunsFrom_args_isRefinedBy ptrModule (fun g _ => hm g) pidFn (hm pidFn)
    (HVector.forall₂_refl (fun v => Ty.isRefinedBy_refl v) p.1) (Memory.Memories.isRefinedBy_refl _)

/-- So `@pcall`, which calls `@pid` on a pointer, is refined with memory in
the module with `@pid`'s new body, with no budget. -/
theorem pcall_replace_isRefinedBy :
    pcallFn.memRuns lay ρ ptrModule ⊑
      (pcallFn.replaceBody pidFn.name pidFn.body).memRuns lay ρ
        (ptrModule.replaceBody pidFn.name pidFn.body) :=
  Core.replaceBody_isRefinedBy_of_from lay ρ ptrModule_valid (by simp [ptrModule, Module.funcs])
    pidFn.body (pid_self_isRefinedBy lay ρ) (by simp [ptrModule, Module.funcs])

/-! # Axioms -/

/-- info: 'FirTest.pcall_replace_isRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.pcall_replace_isRefinedBy

end FirTest
