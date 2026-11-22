import FirTest.TraceArgs

/-!
Tests of refined arguments over the traced runs of a dialect with events,
divergence included (ADR-2026-11-09-1540, the human's ruling of 2026-11-20
on #233):

* the toy emit dialect of `FirTest.TraceDialect` has ops of finitely many
  outcomes, given the world's answers: the answer stream fixes `emit`'s
  answer. So the whole theorem applies to `emitMain`;
* an op that may show `k` events for every `k` does not: against an answer
  stream that goes on forever, it has infinitely many outcomes;
* refined operands: in a dialect whose op `out` shows its operand to the
  world, a function run on poison is refined by the same function run on a
  value, at every outcome, divergence included.
-/

namespace FirTest.TraceDiverge

open Fir Fir.Memory FirTest.TraceDialect FirTest.TraceArgs

/-! # The emit dialect -/

/-- The emit dialect's ops have finitely many outcomes, given the world's
answers: `emit` shows one event, whose answer the stream fixes, and `ret`
returns. -/
theorem emit_traceFinite :
    letI := DialectTrace.traceAt (d := EmitDialect) lay Empty.elim RunItems.empty
    OpsTraceFinite EmitDialect Nat Nat (TraceState Unit (unitsOf lay)) := by
  letI := DialectTrace.traceAt (d := EmitDialect) lay Empty.elim RunItems.empty
  intro op _ args
  cases op with
  | emit =>
    refine ⟨fun _ s ans => ⟨(ans 0).toList.map fun n => (.nil, [⟨(0 : Nat), n⟩], s),
      fun a t s' h hag => ?_⟩, fun h => nomatch h⟩
    obtain ⟨n, he⟩ := (emit_iff args s _).1 h
    simp only [Except.ok.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have := hag 0 _ rfl
    exact List.mem_map.2 ⟨n, by simp [this], rfl⟩
  | ret =>
    refine ⟨(fun h => nomatch h), fun _ s _ => ⟨[(.ret, [], s)], fun a t s' h _ => ?_⟩⟩
    have h : (Except.ok (a, t, s') : TraceEnd (Act Nat Nat) _ Exit) = .ok (.ret, [], s) := h
    cases h
    exact List.mem_singleton_self _

/-- So each outcome of `emitMain`'s traced runs is allowed by its own traced
runs, by the traced layer's theorem for a dialect whose ops show events,
divergence included. -/
example : traceObservable (runs .nil) ⊑ traceObservable (runs .nil) :=
  Func.traceRuns_isRefinedBy_of_args (M := emitModule) (f := emitMain) lay Empty.elim
    RunItems.empty (fun _ => ()) AddrRule.ignore Core.Ty.isRefinedBy_trans emit_traceFinite
    (fun g _ => traceOpsMonotone g) (traceOpsMonotone emitMain) trivial

/-! # An op with any number of events -/

/-- An op that may show the event `0` any number of times, each answered. -/
def manyEmits : TraceM (Act Nat Nat) Unit Unit :=
  fun s e => ∃ (k : Nat) (ns : List Nat), ns.length = k ∧
    e = .ok ((), ns.map fun n => ⟨0, n⟩, s)

/-- It does not have finitely many outcomes, given the world's answers:
against the stream that answers `0` at every place, it has one outcome for
each number of events. -/
theorem manyEmits_not_finite : ¬ TraceFinitelyMany manyEmits := by
  intro h
  obtain ⟨L, hL⟩ := h () fun _ => some 0
  obtain ⟨m, hm⟩ := List.exists_budget (L := L) (Q := fun p m => p.2.1.length ≤ m)
    (fun _ _ _ hle hq => Nat.le_trans hq hle) fun p _ => ⟨p.2.1.length, Nat.le_refl _⟩
  have hmem := hL () ((List.replicate (m + 1) 0).map fun n => ⟨0, n⟩) ()
    ⟨m + 1, _, List.length_replicate .., rfl⟩ fun i a ha => by
      obtain ⟨_, ha⟩ := List.getElem?_eq_some_iff.1 ha
      simp at ha
      rw [← ha]
  have := hm _ hmem
  simp at this
  omega

/-! # Refined operands -/

/-- The ops of the out dialect: `out` shows its operand to the world and
gives no result; `ret` returns nothing. -/
inductive OutOp where
  | out
  | ret
  deriving DecidableEq

/-- A dialect, for these tests, whose op `out` shows its `i8` operand. -/
abbrev OutDialect : Dialect := ⟨OutOp, Core.Ty⟩

instance : DialectSignature OutDialect where
  sig
    | .out => [.int 8]
    | .ret => []
  returnTypes _ := []
  isTerminator
    | .out => false
    | .ret => true
  succCount _ := 0

instance : DialectCall OutDialect := ⟨fun _ => none⟩

/-- The out dialect has no memory. -/
instance : DialectEffects OutDialect :=
  ⟨Empty, fun _ => .exception, fun
    | .out => {}
    | .ret => { control := true }, fun _ => none⟩

/-- An `i8` value of the core. -/
abbrev I8 : Type := ⟦(Core.Ty.int 8 : Core.Ty)⟧

/-- The operand of `out`. -/
def outArg : HVector toType (sig (d := OutDialect) OutOp.out) → I8
  | .cons v .nil => v

/-- The out dialect's events are `i8` values, refined as values, so poison
by any value, and answered by numbers. -/
instance : DialectTrace OutDialect where
  Event := I8
  Answer := Nat
  IsRefinedBy := TyRefinement.IsRefinedBy (t := (Core.Ty.int 8 : Core.Ty))
  traceAt _ _ _ :=
    { denote := fun
        | .out, args => (fun (_ : Nat) => .nil) <$> MonadEvent.emit (outArg args)
        | .ret, _ => MonadUB.ub "ret is a terminator"
      exit := fun
        | .out, _ => MonadUB.ub "out is not a terminator"
        | .ret, _ => pure .ret }

/-- In its traced semantics, `out` shows its operand with any answer, and
keeps the traced state. -/
theorem out_iff (args : HVector toType (sig (d := OutDialect) OutOp.out))
    (s : TraceState Unit (unitsOf lay))
    (e : TraceEnd (DialectTrace.Acts OutDialect) (TraceState Unit (unitsOf lay))
      (HVector toType (returnTypes (d := OutDialect) OutOp.out))) :
    (DialectTrace.traceAt (d := OutDialect) lay Empty.elim RunItems.empty).denote OutOp.out args s e ↔
      ∃ n : Nat, e = .ok (.nil, [⟨outArg args, n⟩], s) := by
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
    exact .inl ⟨n, [⟨outArg args, n⟩], s, _, ⟨n, rfl⟩, rfl, by simp [TraceEnd.after]⟩

/-- The out dialect's ops are monotone in its traced semantics: `out` on an
operand that refines another shows an event that refines the other's, with
the same answer. -/
theorem out_monotone (op : OutDialect.Op) :
    letI := DialectTrace.traceAt (d := OutDialect) lay Empty.elim RunItems.empty
    OpTraceMonotone (d := OutDialect) (B := DialectTrace.Acts OutDialect)
      (σ := TraceState Unit (unitsOf lay)) op := by
  letI := DialectTrace.traceAt (d := OutDialect) lay Empty.elim RunItems.empty
  intro args args' hargs
  cases op with
  | out =>
    refine ⟨fun _ s s' hs e' he' => ?_, fun h => nomatch h⟩
    obtain ⟨n, rfl⟩ := (out_iff args' s' e').1 he'
    refine ⟨.ok (.nil, [⟨outArg args, n⟩], s), (out_iff args s _).2 ⟨n, rfl⟩, trivial,
      ⟨⟨?_, rfl⟩, trivial⟩, hs⟩
    cases args with
    | cons v vs =>
      cases vs
      cases args' with
      | cons v' vs' =>
        cases vs'
        exact hargs.1
  | ret =>
    refine ⟨(fun h => nomatch h), fun _ s s' hs e' he' => ?_⟩
    have he' : e' = .ok (.ret, [], s') := he'
    subst he'
    exact ⟨.ok (.ret, [], s), rfl, rfl, trivial, hs⟩

/-- The out dialect's ops have finitely many outcomes, given the world's
answers. -/
theorem out_traceFinite :
    letI := DialectTrace.traceAt (d := OutDialect) lay Empty.elim RunItems.empty
    OpsTraceFinite OutDialect I8 Nat (TraceState Unit (unitsOf lay)) := by
  letI := DialectTrace.traceAt (d := OutDialect) lay Empty.elim RunItems.empty
  intro op _ args
  cases op with
  | out =>
    refine ⟨fun _ s ans => ⟨(ans 0).toList.map fun n => (.nil, [⟨outArg args, n⟩], s),
      fun a t s' h hag => ?_⟩, fun h => nomatch h⟩
    obtain ⟨n, he⟩ := (out_iff args s _).1 h
    simp only [Except.ok.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have := hag 0 _ rfl
    exact List.mem_map.2 ⟨n, by simp [this], rfl⟩
  | ret =>
    refine ⟨(fun h => nomatch h), fun _ s _ => ⟨[(.ret, [], s)], fun a t s' h _ => ?_⟩⟩
    have h : (Except.ok (a, t, s') : TraceEnd (Act I8 Nat) _ Exit) = .ok (.ret, [], s) := h
    cases h
    exact List.mem_singleton_self _

/-- A function of the out dialect that shows its parameter, then returns. -/
def outMain : Func OutDialect where
  name := "main"
  params := [("x", .int 8)]
  results := []
  body := { blocks := [{ label := "entry", params := [], body :=
    [{ results := [], op := .out, operands := ["x"], succs := [], regions := [], loc := 0 },
      { results := [], op := .ret, operands := [], succs := [], regions := [], loc := 0 }] }] }

/-- A module of the out dialect with that one function. -/
def outModule : Module OutDialect := { items := [.func outMain], locs := [(0, .unknown)] }

/-- The spec's traced runs of `outMain`. -/
abbrev outRuns : FuncTraceRuns (HVector toType ([.int 8] : List Core.Ty))
    (DialectTrace.Acts OutDialect) (ObservedEnd (unitsOf lay) (fun _ => ()) (List (DVal OutDialect))) :=
  outMain.observedRuns lay Empty.elim RunItems.empty (fun _ => ()) outModule

/-- Refined operands: `outMain` run on poison is refined by `outMain` run on
the value `5`, at every outcome, divergence included. The source shows the
event poison where the target shows `5`, and gets the same answer. -/
theorem outMain_poison_isRefinedBy :
    traceObservable (outRuns (.cons .poison .nil)) ⊑
      traceObservable (outRuns (.cons (.value 5) .nil)) :=
  Func.traceRuns_isRefinedBy_of_args (M := outModule) (f := outMain) lay Empty.elim
    RunItems.empty (fun _ => ()) AddrRule.ignore Core.Ty.isRefinedBy_trans out_traceFinite
    (fun _ _ _ _ o _ _ => out_monotone o.op) (fun _ _ o _ _ => out_monotone o.op) ⟨trivial, trivial⟩

/-! # Axioms -/

/-- info: 'Fir.Func.traceRuns_isRefinedBy_of_args' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.traceRuns_isRefinedBy_of_args

/-- info: 'FirTest.TraceDiverge.outMain_poison_isRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.TraceDiverge.outMain_poison_isRefinedBy

end FirTest.TraceDiverge
