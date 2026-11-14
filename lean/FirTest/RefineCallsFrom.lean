import FirTest.RefineCalls

/-!
Tests of congruence in the callee from given memories, applied to the module
of `@count` and `@g` of `FirTest.RefineCalls`, and the axioms of its proofs
and of the forms for a callee that touches no memory: `@g` given a body with
no blocks meets the hypothesis, with no budget, so `@count` is refined with
memory by itself, by the form for every function and by the caller form.
-/

namespace FirTest

open Fir Core Example

/-! # A body with no blocks

From given memories, congruence asks that the new `@g` refine the old from
every memories, and no budget. A body with no blocks meets it: `@g` with it
never starts, so it has no behaviour. So `@count` is refined with memory by
itself in the module with that body. -/

/-- A body with no blocks: a function with it never starts. -/
def noBlocks : Region CoreDialect := { blocks := [] }

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem CoreDialect → N)

/-- A function given no blocks, in its module so changed, has no outcome
from any memories: each path is stuck. -/
theorem noBlocks_outcomes (M : Module CoreDialect) (g : Func CoreDialect)
    (a : HVector toType (g.params.map (·.2))) (S : Memory.Memories N (unitsOf lay)) (m : Nat)
    (o : Outcome (List (DVal CoreDialect) × Memory.Memories N (unitsOf lay))) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
    ¬ ((g.replaceBody g.name noBlocks).memRunsFrom (M.replaceBody g.name noBlocks)
      (a, S) m).outcomes o := by
  letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
  have key : ∀ x, Ev.NotStuck x → ¬ ((g.replaceBody g.name noBlocks).memRunsFrom
      (M.replaceBody g.name noBlocks) (a, S) m) x := by
    intro x hx h
    obtain ⟨p, hp, -⟩ := (Func.memRunsFrom_run hx).1 h
    simp [Func.enter, Func.blocks, noBlocks, stuck] at hp
  cases o with
  | ret _ => exact key _ fun _ h => nomatch h
  | ub _ => exact key _ fun _ h => nomatch h
  | fuelExhausted => exact key _ fun _ h => nomatch h

/-- A function given no blocks, in its module so changed, refines itself
from given memories: it has no behaviour. -/
theorem noBlocks_isRefinedBy (M : Module CoreDialect) (g : Func CoreDialect) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
    g.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
      (g.replaceBody g.name noBlocks).memRunsFrom (Mem := N) (unit := unitsOf lay)
        (M.replaceBody g.name noBlocks) := by
  letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
  intro ⟨a, S⟩ t ht
  cases t with
  | ret o => obtain ⟨n, hn⟩ := ht; exact (noBlocks_outcomes lay ρ M g a S n (.ret o) hn).elim
  | ub r => obtain ⟨n, hn⟩ := ht; exact (noBlocks_outcomes lay ρ M g a S n (.ub r) hn).elim
  | fuelExhausted => exact (noBlocks_outcomes lay ρ M g a S 0 .fuelExhausted (ht 0)).elim

/-- A function given no blocks, in its module so changed, refines itself
with memory. -/
theorem noBlocks_memIsRefinedBy (M : Module CoreDialect) (g : Func CoreDialect) :
    g.memRuns lay ρ M ⊑
      (g.replaceBody g.name noBlocks).memRuns lay ρ (M.replaceBody g.name noBlocks) :=
  fun a => Func.memRuns_isRefinedBy_of_from lay ρ (noBlocks_isRefinedBy lay ρ M g (a, _))

/-- `@count` is refined with memory by itself in the module where `@g` has
no blocks, with no budget: every core op has finitely many outcomes. -/
theorem count_fromIsRefinedBy :
    countFn.memRuns ubModule.layout.entry id ubModule ⊑
      (countFn.replaceBody gFn.name noBlocks).memRuns ubModule.layout.entry id
        (ubModule.replaceBody gFn.name noBlocks) :=
  Core.replaceBody_isRefinedBy_of_from _ _ ubModule_valid (by simp [ubModule, Module.funcs])
    noBlocks (noBlocks_isRefinedBy _ _ ubModule gFn) (by simp [ubModule, Module.funcs])

/-- And `@count` is refined with memory by itself in the module where `@g`
has no blocks, by the caller form. -/
theorem count_callerIsRefinedBy :
    countFn.memRuns ubModule.layout.entry id ubModule ⊑
      countFn.memRuns ubModule.layout.entry id (ubModule.replaceBody gFn.name noBlocks) :=
  Core.caller_isRefinedBy_of_from _ _ ubModule_valid (by simp [ubModule, Module.funcs])
    noBlocks (noBlocks_isRefinedBy _ _ ubModule gFn) (by simp [ubModule, Module.funcs])
    (by decide)

/-! # Axioms -/

/-- info: 'Fir.Func.memRunsFrom_boundedBy_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.memRunsFrom_boundedBy_of_finite

/-- info: 'Fir.Func.memRuns_replaceBody_isRefinedBy_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.memRuns_replaceBody_isRefinedBy_of_finite

/-- info: 'Fir.Core.replaceBody_isRefinedBy_of_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.replaceBody_isRefinedBy_of_from

/-- info: 'FirTest.count_callerIsRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.count_callerIsRefinedBy

/-- info: 'FirTest.count_fromIsRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.count_fromIsRefinedBy

/-- info: 'Fir.Module.memOps_ignoresMemory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Module.memOps_ignoresMemory

end FirTest
