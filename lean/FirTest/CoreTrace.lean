import FirTest.RefineCallsFrom

/-!
Tests of the core's traced runs (#233, stage 3a), and the axioms of their
proofs. No core op shows an event, and no run makes an external call yet
(#239), so its traced semantics lifts its semantics with memory:

* the traced behaviour of `@fact` is its behaviour with memory, each return
  seen at its end, with an empty trace;
* refined arguments over traced runs: `@fact`, which calls itself, on a
  poison argument is refined by `@fact` on `5`, and so at every world;
* congruence in the callee over traced runs: `@count` is refined by itself
  in the module where `@g` has no blocks (`FirTest.RefineCallsFrom`), and so
  at every world. The traced layer's own theorem proves it (stage 3c-2b),
  from the hypothesis with memory that `@g` meets.
-/

namespace FirTest

open Fir Core Example

/-! # Traced runs of the core -/

/-- The traced behaviour of `@fact`, run as the modes run it, is its behaviour
with memory, each return seen at its end, with an empty trace. -/
example (a : HVector toType (factFn.params.map (·.2))) :
    traceObservable (factFn.observedRuns recModule.layout.entry id recModule.runItems id recModule
        a) =
      .ofBehaviour (observable (factFn.memEndRuns recModule.layout.entry id recModule.runItems id
        AddrRule.ignore recModule a)) :=
  Func.traceObservable_traceRuns _ _ _ _ _ recModule factFn a

/-! # Refined arguments -/

/-- `@fact` on a poison argument is refined by `@fact` on `5`, over traced
runs. -/
theorem fact_traceArgs :
    traceObservable (factFn.observedRuns recModule.layout.entry id recModule.runItems id recModule
        (.cons .poison .nil)) ⊑
      traceObservable (factFn.observedRuns recModule.layout.entry id recModule.runItems id
        recModule (.cons (.value 5) .nil)) :=
  Core.trace_args_isRefinedBy _ _ _ _ recModule factFn ⟨trivial, trivial⟩

/-- And at every world: each outcome of `@fact` on `5` at a world is allowed
by an outcome of `@fact` on a poison argument. -/
theorem fact_traceArgs_world :
    ∀ w t, (traceObservable (factFn.observedRuns recModule.layout.entry id recModule.runItems id
        recModule (.cons (.value 5) .nil))).atWorld w t →
      ∃ s, traceObservable (factFn.observedRuns recModule.layout.entry id recModule.runItems id
        recModule (.cons .poison .nil)) s ∧ s ⊑ t :=
  Core.trace_args_isRefinedBy_world _ _ _ _ recModule factFn ⟨trivial, trivial⟩

/-! # Congruence in the callee -/

/-- `@count` is refined by itself over traced runs in the module where `@g`
has no blocks, with no budget. -/
theorem count_traceIsRefinedBy (L : RunItems) :
    countFn.observedRuns ubModule.layout.entry id L id ubModule ⊑
      (countFn.replaceBody gFn.name noBlocks).observedRuns ubModule.layout.entry id L id
        (ubModule.replaceBody gFn.name noBlocks) :=
  Core.trace_replaceBody_isRefinedBy_of_from _ _ L _ ubModule_valid
    (by simp [ubModule, Module.funcs]) noBlocks (noBlocks_isRefinedBy _ _ L ubModule gFn)
    (by simp [ubModule, Module.funcs])

/-- And at every world. -/
theorem count_traceIsRefinedBy_world (L : RunItems) :
    ∀ a w t, (traceObservable ((countFn.replaceBody gFn.name noBlocks).observedRuns
        ubModule.layout.entry id L id (ubModule.replaceBody gFn.name noBlocks) a)).atWorld w t →
      ∃ s, traceObservable (countFn.observedRuns ubModule.layout.entry id L id ubModule a) s ∧
        s ⊑ t :=
  Core.trace_replaceBody_isRefinedBy_of_from_world _ _ L _ ubModule_valid
    (by simp [ubModule, Module.funcs]) noBlocks (noBlocks_isRefinedBy _ _ L ubModule gFn)
    (by simp [ubModule, Module.funcs])

/-! # Axioms -/

/-- info: 'Fir.End.isRefinedBy_of_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.End.isRefinedBy_of_mem

/-- info: 'Fir.Func.traceRuns_isRefinedBy_of_from' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.traceRuns_isRefinedBy_of_from

/-- info: 'Fir.Core.trace_args_isRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.trace_args_isRefinedBy

/-- info: 'Fir.Core.trace_args_isRefinedBy_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.trace_args_isRefinedBy_world

/-- info: 'Fir.Func.traceRunsFrom_isRefinedBy_of_memRunsFrom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.traceRunsFrom_isRefinedBy_of_memRunsFrom

/-- info: 'Fir.Func.traceRunsFrom_noActs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.traceRunsFrom_noActs

/-- info: 'Fir.Core.trace_replaceBody_isRefinedBy_of_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.trace_replaceBody_isRefinedBy_of_from

/-- info: 'Fir.Core.trace_replaceBody_isRefinedBy_of_from_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.trace_replaceBody_isRefinedBy_of_from_world

/-- info: 'FirTest.fact_traceArgs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.fact_traceArgs

/-- info: 'FirTest.count_traceIsRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.count_traceIsRefinedBy

/-- info: 'FirTest.fact_traceArgs_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.fact_traceArgs_world

/-- info: 'FirTest.count_traceIsRefinedBy_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.count_traceIsRefinedBy_world

/-- info: 'Fir.Func.traceRuns_args_isRefinedBy_of_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.traceRuns_args_isRefinedBy_of_lawful

/-- info: 'Fir.Func.traceRuns_replaceBody_isRefinedBy_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.traceRuns_replaceBody_isRefinedBy_of_bound

/-- info: 'Fir.Func.traceRuns_replaceBody_isRefinedBy_of_opsFinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.traceRuns_replaceBody_isRefinedBy_of_opsFinite

/-- info: 'Fir.Gpu.trace_args_isRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Gpu.trace_args_isRefinedBy

/-- info: 'Fir.Gpu.trace_args_isRefinedBy_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Gpu.trace_args_isRefinedBy_world

/-- info: 'Fir.Gpu.trace_replaceBody_isRefinedBy_of_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Gpu.trace_replaceBody_isRefinedBy_of_from

/-- info: 'Fir.Gpu.trace_replaceBody_isRefinedBy_of_from_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Gpu.trace_replaceBody_isRefinedBy_of_from_world

end FirTest
