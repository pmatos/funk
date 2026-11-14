import FirTest.RefineCalls

/-!
Tests of congruence in the callee from given memories, applied to the module
of `@count` and `@g` of `FirTest.RefineCalls`, and the axioms of its proofs:
`@g` given a body with no blocks meets the hypotheses of both forms, with no
budget for a callee that touches no memory, and with one for a callee that
may touch memory, so `@count` is refined with memory by itself.
-/

namespace FirTest

open Fir Core Example

/-! # A body with no blocks

From given memories, congruence asks that the new `@g` refine the old from
every memories, and, for a callee that touches memory, that its runs be
bounded. A body with no blocks meets both: `@g` with it never starts, so it
has no behaviour, no run of it runs out of fuel, and it reaches no memory. So `@count` is refined with memory by itself in
the module with that body, by each form. -/

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

/-- `@g` with no blocks, in its module so changed, refines `@g` from given
memories: it has no behaviour. -/
theorem noBlocks_isRefinedBy :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) ubModule.layout.entry id
    gFn.memRunsFrom (Mem := Nat) (unit := unitsOf ubModule.layout.entry) ubModule ⊑
      (gFn.replaceBody gFn.name noBlocks).memRunsFrom (Mem := Nat)
        (unit := unitsOf ubModule.layout.entry) (ubModule.replaceBody gFn.name noBlocks) := by
  letI := DialectMemDenote.denoteAt (d := CoreDialect) ubModule.layout.entry id
  intro ⟨a, S⟩ t ht
  cases t with
  | ret o => obtain ⟨n, hn⟩ := ht; exact (noBlocks_outcomes a S n (.ret o) hn).elim
  | ub r => obtain ⟨n, hn⟩ := ht; exact (noBlocks_outcomes a S n (.ub r) hn).elim
  | fuelExhausted => exact (noBlocks_outcomes a S 0 .fuelExhausted (ht 0)).elim

/-- `@count` is refined with memory by itself in the module where `@g` has
no blocks, with no budget: every core op has finitely many outcomes. -/
theorem count_fromIsRefinedBy :
    countFn.memRuns ubModule.layout.entry id ubModule ⊑
      (countFn.replaceBody gFn.name noBlocks).memRuns ubModule.layout.entry id
        (ubModule.replaceBody gFn.name noBlocks) :=
  Core.replaceBody_isRefinedBy_of_from _ _ ubModule_valid (by simp [ubModule, Module.funcs])
    noBlocks noBlocks_isRefinedBy (by simp [ubModule, Module.funcs])

/-- `@count` is refined with memory by itself in the module where `@g` has
no blocks, with a budget. -/
theorem count_memIsRefinedBy :
    countFn.memRuns ubModule.layout.entry id ubModule ⊑
      countFn.memRuns ubModule.layout.entry id (ubModule.replaceBody gFn.name noBlocks) := by
  letI := DialectMemDenote.denoteAt (d := CoreDialect) ubModule.layout.entry id
  exact Core.memCaller_isRefinedBy _ _ ubModule_valid (by simp [ubModule, Module.funcs])
    noBlocks ⟨0, fun ⟨a, S⟩ => .inr fun m _ => noBlocks_outcomes a S m .fuelExhausted⟩
    noBlocks_isRefinedBy (by simp [ubModule, Module.funcs]) (by decide)

/-! # Axioms -/

/-- info: 'Fir.Func.memRunsFrom_boundedBy_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.memRunsFrom_boundedBy_of_finite

/-- info: 'Fir.Func.memRuns_replaceBody_isRefinedBy_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.memRuns_replaceBody_isRefinedBy_of_finite

/-- info: 'Fir.Core.replaceBody_isRefinedBy_of_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.replaceBody_isRefinedBy_of_from

/-- info: 'Fir.Core.memReplaceBody_isRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.memReplaceBody_isRefinedBy

/-- info: 'FirTest.count_memIsRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.count_memIsRefinedBy

/-- info: 'FirTest.count_fromIsRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.count_fromIsRefinedBy

/-- info: 'Fir.Module.memOps_ignoresMemory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Module.memOps_ignoresMemory

end FirTest
