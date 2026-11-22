import FirTest.TraceDialect

/-!
Tests of refined arguments over the traced runs of a dialect with events
(ADR-2026-11-09-1540): the toy emit dialect of `FirTest.TraceDialect`, whose
op `emit` shows the event `0` to the world and gets any answer, has ops
monotone in the traced layer. So the traced layer's own theorems apply to
it: each return of `emitMain` is allowed by one of its own returns or by UB
after acts that the return first shows.
-/

namespace FirTest.TraceArgs

open Fir Fir.Memory FirTest.TraceDialect

/-- In its traced semantics, `emit` shows the event `0` with any answer, and
keeps the traced state. -/
theorem emit_iff (args : HVector toType (sig (d := EmitDialect) EmitOp.emit))
    (s : TraceState Unit (unitsOf lay))
    (e : TraceEnd (DialectTrace.Acts EmitDialect) (TraceState Unit (unitsOf lay))
      (HVector toType (returnTypes (d := EmitDialect) EmitOp.emit))) :
    (DialectTrace.traceAt (d := EmitDialect) lay Empty.elim RunItems.empty).denote EmitOp.emit args s e ↔
      ∃ n : Nat, e = .ok (.nil, [⟨(0 : Nat), n⟩], s) := by
  dsimp only [DialectDenote.denote, DialectTrace.traceAt]
  rw [map_eq_pure_bind, TraceM.bind_apply]
  constructor
  · rintro (⟨a, t, s₁, e₁, ⟨n, he⟩, he₁, rfl⟩ | ⟨_, _, ⟨_, he⟩, _⟩)
    · simp only [Except.ok.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have he₁ : e₁ = _ := he₁
      subst he₁
      exact ⟨a, by simp [TraceEnd.after]⟩
    · cases he
  · rintro ⟨n, rfl⟩
    exact .inl ⟨n, [⟨(0 : Nat), n⟩], s, _, ⟨n, rfl⟩, rfl, by simp [TraceEnd.after]⟩

/-- The emit dialect's ops are monotone in its traced semantics: `emit`
shows the same event, with the same answer, from a traced state that
refines another, and `ret` goes to the same place. -/
theorem emit_monotone (op : EmitDialect.Op) :
    letI := DialectTrace.traceAt (d := EmitDialect) lay Empty.elim RunItems.empty
    OpTraceMonotone (d := EmitDialect) (B := DialectTrace.Acts EmitDialect)
      (σ := TraceState Unit (unitsOf lay)) op := by
  letI := DialectTrace.traceAt (d := EmitDialect) lay Empty.elim RunItems.empty
  intro args args' _
  cases op with
  | emit =>
    refine ⟨fun _ s s' hs e' he' => ?_, fun h => nomatch h⟩
    obtain ⟨n, rfl⟩ := (emit_iff args' s' e').1 he'
    refine ⟨.ok (.nil, [⟨(0 : Nat), n⟩], s), (emit_iff args s _).2 ⟨n, rfl⟩, ?_⟩
    refine ⟨trivial, ?_, hs⟩
    exact List.isRefinedBy_refl (fun x : DialectTrace.Acts EmitDialect => Act.isRefinedBy_refl
      (fun _ => (rfl : _ = _)) x) _
  | ret =>
    constructor
    · intro h
      cases h
    intro _ s s' hs e' he'
    have he' : e' = .ok (.ret, [], s') := he'
    subst he'
    refine ⟨.ok (.ret, [], s), ?_, ?_⟩
    · rfl
    · refine ⟨rfl, ?_, ?_⟩
      · exact trivial
      · exact hs

/-- Every function of the emit dialect has its ops monotone in the traced
layer. -/
theorem traceOpsMonotone (g : Func EmitDialect) :
    letI := DialectTrace.traceAt (d := EmitDialect) lay Empty.elim RunItems.empty
    g.TraceOpsMonotone (DialectTrace.Acts EmitDialect) (TraceState Unit (unitsOf lay)) :=
  letI := DialectTrace.traceAt (d := EmitDialect) lay Empty.elim RunItems.empty
  fun _ _ o _ => ⟨fun _ => emit_monotone o.op,
    fun _ _ _ => ExtTraceMonotone.of_ub (fun _ _ _ => rfl) _ _ _⟩

/-- So each return of `emitMain`'s traced runs is allowed by its own traced
runs, by the traced layer's theorem for a dialect whose ops show events. -/
example (tr : List (DialectTrace.Acts EmitDialect))
    (o : ObservedEnd (unitsOf lay) (fun _ => ()) (List (DVal EmitDialect)))
    (h : traceObservable (runs .nil) (.ret tr o)) :
    ∃ s : TOutcome (DialectTrace.Acts EmitDialect)
        (ObservedEnd (unitsOf lay) (fun _ => ()) (List (DVal EmitDialect))),
      traceObservable (runs .nil) s ∧ s ⊑ (.ret tr o : TOutcome (DialectTrace.Acts EmitDialect) _) :=
  Func.traceRuns_ret_allowed (M := emitModule) (f := emitMain) (a := .nil) (a' := .nil) lay Empty.elim RunItems.empty (fun _ => ())
    AddrRule.ignore
    Core.Ty.isRefinedBy_trans (fun g _ => traceOpsMonotone g) (traceOpsMonotone emitMain) trivial h

end FirTest.TraceArgs
