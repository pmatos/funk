import FirTest.TraceDiverge

/-!
Tests of the engine of congruence in the callee over the traced runs of a
dialect with events, without divergence (ADR-2026-11-09-1540, stage 3c-1 of
#233), on the toy emit dialect of `FirTest.TraceDialect`, whose op `emit`
shows the event `0` to the world:

* refined arguments from a given traced state: `emitMain`, run from a traced
  state in which an allocation escaped, refines itself, divergence included;
* replacing `emitMain`'s body by itself, which refines it, gives a module
  that runs each call as `emitModule` does, in the traced layer;
* so each return and each UB of `emitMain`'s traced runs in that module is
  allowed by its traced runs in `emitModule`.
-/

namespace FirTest.TraceCallee

open Fir Fir.Memory FirTest.TraceDialect FirTest.TraceArgs FirTest.TraceDiverge

/-- Refinement of the emit dialect's typed values is reflexive. -/
theorem dval_refl (x : DVal EmitDialect) : x ⊑ x := ⟨rfl, Core.Ty.isRefinedBy_refl _⟩

/-- A traced state in which one allocation of the one memory escaped. -/
abbrev escaped : TraceState Unit (unitsOf lay) := ⟨Memories.empty, [((), 0)]⟩

/-- `emitMain`'s traced runs from a traced state in which an allocation
escaped refine themselves, the traced state each return ends in included:
refined arguments from a given traced state, divergence included. -/
example : traceObservable (emitMain.traceRunsFrom lay Empty.elim RunItems.empty emitModule
      (.nil, escaped)) ⊑
    traceObservable (emitMain.traceRunsFrom lay Empty.elim RunItems.empty emitModule
      (.nil, escaped)) :=
  Func.traceRunsFrom_isRefinedBy_of_args lay Empty.elim RunItems.empty emit_traceFinite
    (fun g _ => traceOpsMonotone g) (traceOpsMonotone emitMain) trivial
    (TraceState.isRefinedBy_refl _)

/-- `emitMain` with its own body, in `emitModule` with that body, refines
`emitMain` in `emitModule`, from every traced state: replacing a body by
itself changes neither, as the kernel computes. -/
theorem self_isRefinedBy :
    emitMain.traceRunsFrom lay Empty.elim RunItems.empty emitModule ⊑
      (emitMain.replaceBody emitMain.name emitMain.body).traceRunsFrom lay Empty.elim
        RunItems.empty (emitModule.replaceBody emitMain.name emitMain.body) := by
  exact FuncTraceRuns.isRefinedBy_refl (Act.isRefinedBy_refl fun _ => rfl)
    (fun o : List (DVal EmitDialect) × TraceState Unit (unitsOf lay) =>
      (⟨List.isRefinedBy_refl dval_refl o.1, TraceState.isRefinedBy_refl o.2⟩ : o ⊑ o)) _

/-- Replacing `emitMain`'s body by one that refines it gives a module that
runs each call as `emitModule` does, in the traced layer. -/
theorem callsRefined :
    letI := DialectTrace.stepAt (d := EmitDialect) lay Empty.elim RunItems.empty
    TraceCallsRefined (DialectTrace.Acts EmitDialect) Unit (unitsOf lay) emitModule
      (emitModule.replaceBody emitMain.name emitMain.body) :=
  Module.replaceBody_traceCallsRefined lay Empty.elim RunItems.empty emit_traceFinite
    (fun g _ => traceOpsMonotone g) Core.Ty.isRefinedBy_trans (fun h₁ h₂ => h₁.trans h₂)
    (by decide) (List.mem_singleton_self _) _ self_isRefinedBy

/-- So each return of `emitMain`'s traced runs in the module with its body
replaced is allowed by its traced runs in `emitModule`. -/
example (tr : List (DialectTrace.Acts EmitDialect))
    (o : ObservedEnd (unitsOf lay) (fun _ => ()) (List (DVal EmitDialect)))
    (h : traceObservable (emitMain.observedRuns lay Empty.elim RunItems.empty (fun _ => ())
      (emitModule.replaceBody emitMain.name emitMain.body) .nil) (.ret tr o)) :
    ∃ t, traceObservable (runs .nil) t ∧
      t ⊑ (.ret tr o : TOutcome (DialectTrace.Acts EmitDialect) _) :=
  Func.traceRuns_calls_ret_allowed lay Empty.elim RunItems.empty (fun _ => ()) AddrRule.ignore
    Core.Ty.isRefinedBy_trans (fun g _ => traceOpsMonotone g) callsRefined
    (traceOpsMonotone emitMain) (by exact trivial) h

/-- And each UB of `emitMain`'s traced runs in that module is allowed by UB
of its traced runs in `emitModule`. -/
example (tr : List (DialectTrace.Acts EmitDialect)) (r : String)
    (h : traceObservable (emitMain.observedRuns lay Empty.elim RunItems.empty (fun _ => ())
      (emitModule.replaceBody emitMain.name emitMain.body) .nil) (.ub tr r)) :
    ∃ t, traceObservable (runs .nil) t ∧
      t ⊑ (.ub tr r : TOutcome (DialectTrace.Acts EmitDialect)
        (ObservedEnd (unitsOf lay) (fun _ => ()) (List (DVal EmitDialect)))) :=
  Func.traceRuns_calls_ub_allowed lay Empty.elim RunItems.empty (fun _ => ()) AddrRule.ignore
    (fun g _ => traceOpsMonotone g) callsRefined (traceOpsMonotone emitMain) (by exact trivial) h

end FirTest.TraceCallee
