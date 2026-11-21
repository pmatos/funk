import Fir

/-!
Tests of a dialect's traced runs with a toy event (ADR-2026-11-09-1540): a
dialect whose op `emit` shows the event `0` to the world, and whose op
`ret` returns. The traced runs of a function that emits, then returns, go
through the interpreter in the traced layer of marked traces: each op shows
its step before its acts, and erasing the steps gives the dialect's own
runs.
-/

namespace FirTest.TraceDialect

open Fir Fir.Memory

/-- The ops of the emit dialect: `emit` shows an event and gives no result;
`ret` returns nothing. -/
inductive EmitOp where
  | emit
  | ret
  deriving DecidableEq

/-- A dialect, for these tests, whose op `emit` shows an event. -/
abbrev EmitDialect : Dialect := ⟨EmitOp, Core.Ty⟩

instance : DialectSignature EmitDialect where
  sig _ := []
  returnTypes _ := []
  isTerminator
    | .emit => false
    | .ret => true
  succCount _ := 0

instance : DialectCall EmitDialect := ⟨fun _ => none⟩

/-- The emit dialect has no memory. -/
instance : DialectEffects EmitDialect :=
  ⟨Empty, fun _ => .exception, fun
    | .emit => {}
    | .ret => { control := true }, fun _ => none⟩

/-- The emit dialect's events are numbers, answered by numbers: `emit`
shows `0`, and `ret` returns. -/
instance : DialectTrace EmitDialect where
  Event := Nat
  Answer := Nat
  IsRefinedBy := Eq
  traceAt _ _ _ :=
    { denote := fun
        | .emit, _ => (fun (_ : Nat) => .nil) <$> MonadEvent.emit (0 : Nat)
        | .ret, _ => MonadUB.ub "ret is a terminator"
      exit := fun
        | .emit, _ => MonadUB.ub "emit is not a terminator"
        | .ret, _ => pure .ret }

/-- The ops of a block that emits, then returns. -/
def emitOps : List (Operation EmitDialect) :=
  [{ results := [], op := .emit, operands := [], succs := [], regions := [], loc := 0 },
    { results := [], op := .ret, operands := [], succs := [], regions := [], loc := 0 }]

/-- A function of the emit dialect that emits, then returns. -/
def emitMain : Func EmitDialect where
  name := "main"
  params := []
  results := []
  body := { blocks := [{ label := "entry", params := [], body := emitOps }] }

/-- A module of the emit dialect with that one function. -/
def emitModule : Module EmitDialect := { items := [.func emitMain], locs := [(0, .unknown)] }

/-- The layout of the one memory of a run of the emit dialect, which has no
memory of its own. -/
abbrev lay : Unit → MemLayout := fun _ => MemLayout.default

/-- The spec's traced runs of `emitMain`, with no memory of its own, each
return seen at its end. -/
abbrev runs : FuncTraceRuns (HVector toType ([] : List Core.Ty)) (DialectTrace.Acts EmitDialect)
    (ObservedEnd (unitsOf lay) (fun _ => ()) (List (DVal EmitDialect))) :=
  emitMain.observedRuns lay Empty.elim RunItems.empty (fun _ => ()) emitModule

/-- The traced state inside the call of `emitMain`: a frame entered, and
nothing escaped. -/
abbrev inCall : TraceState Unit (unitsOf lay) := ⟨Memories.empty.enter, []⟩

/-! # Paths of the traced layer, with stuck paths -/

section Paths

variable {A σ ε α β : Type}

/-- A sequence ends as its first computation's result followed by its
second's end, after the first's trace. -/
theorem run_bind {x : ExceptT ε (TraceM A σ) α} {f : α → ExceptT ε (TraceM A σ) β} {s s' : σ}
    {a : α} {t : List A} {e' e : TraceEnd A σ (Except ε β)}
    (hx : x.run s (.ok (.ok a, t, s'))) (hf : (f a).run s' e') (he : e = e'.after t) :
    (x >>= f).run s e :=
  ⟨_, hx, e', hf, he⟩

/-- `pure` ends with its value, showing nothing. -/
theorem run_pure (a : α) (s : σ) : (pure a : ExceptT ε (TraceM A σ) α).run s (.ok (.ok a, [], s)) :=
  rfl

/-- A step of the interpreter that cannot get stuck ends with its value,
showing nothing. -/
theorem run_liftExcept (a : α) (s : σ) :
    (liftExcept (Except.ok a : Except ε α) : ExceptT ε (TraceM A σ) α).run s (.ok (.ok a, [], s)) :=
  rfl

/-- An op's rule, lifted, ends as the rule does. -/
theorem run_lift {x : TraceM A σ α} {s s' : σ} {a : α} {t : List A}
    (hx : x s (.ok (a, t, s'))) : (ExceptT.lift x : ExceptT ε (TraceM A σ) α).run s (.ok (.ok a, t, s')) :=
  ⟨_, hx, _, rfl, by simp [TraceEnd.after]⟩

end Paths

/-- With enough fuel, `emitMain` shows the step of `emit`, then its act with
any answer, then the step of `ret`, and returns: the interpreter marks each
op's step before the op's acts. -/
theorem emitMain_run (a : Nat) :
    runs .nil 2 (.ok (.ok (.ret ⟨[], Memories.empty, []⟩),
      [.tick, .act (⟨0, a⟩ : Act Nat Nat), .tick])) := by
  letI := DialectTrace.stepAt (d := EmitDialect) lay Empty.elim RunItems.empty
  refine ⟨.ok (.ok (.ret []), [.tick, .act (⟨0, a⟩ : Act Nat Nat), .tick], (TraceState.init Memories.empty)), ?_,
    rfl⟩
  unfold Func.run
  refine run_bind (a := (emitOps, [])) (t := []) (s' := (TraceState.init Memories.empty))
    (run_liftExcept _ _) ?_ (TraceEnd.after_nil _).symm
  refine run_bind (a := Result.ret ([], 0))
    (t := [Step.tick, Step.act (⟨0, a⟩ : Act Nat Nat), Step.tick])
    (s' := (TraceState.init Memories.empty))
    ⟨.ok (.ok (Result.ret ([], 0)), [Step.tick, Step.act (⟨0, a⟩ : Act Nat Nat), Step.tick],
      inCall), ?_, rfl⟩ (run_pure _ _) (by simp [TraceEnd.after])
  simp only [emitOps]
  unfold Func.runOps
  simp only [Operation.ownsCoreRegion, List.any_nil, Bool.false_eq_true, ite_false, sig,
    isTerminator, callee?]
  refine run_bind (a := HVector.nil) (run_liftExcept _ _) ?_ (TraceEnd.after_nil _).symm
  refine run_bind (a := HVector.nil) (t := [Step.tick, Step.act (⟨0, a⟩ : Act Nat Nat)])
    (s' := inCall)
    (e' := .ok (.ok (Result.ret ([], 0)), [Step.tick], inCall))
    (run_lift ?_) ?_ (by simp [TraceEnd.after])
  · refine ⟨_, rfl, _, ⟨.ok (HVector.nil, [(⟨0, a⟩ : Act Nat Nat)], inCall), ?_, rfl⟩, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, _, rfl, rfl⟩
  refine run_bind (a := []) (run_liftExcept _ _) ?_ (TraceEnd.after_nil _).symm
  unfold Func.runOps
  simp only [Operation.ownsCoreRegion, List.any_nil, Bool.false_eq_true, ite_false, sig,
    isTerminator, ite_true, List.isEmpty_nil, Bool.not_true]
  refine run_bind (a := HVector.nil) (run_liftExcept _ _) ?_ (TraceEnd.after_nil _).symm
  refine run_bind (a := Exit.ret) (t := [Step.tick]) (s' := inCall)
    (e' := .ok (.ok (Result.ret ([], 0)), [], inCall))
    (run_lift ⟨_, rfl, _, ⟨_, rfl, rfl⟩, rfl⟩) ?_ (by simp [TraceEnd.after])
  exact run_pure _ _

/-- So `emitMain`'s traced behaviour returns after the act of `emit`, with
any answer. -/
example (a : Nat) :
    traceObservable (runs .nil) (.ret [(⟨0, a⟩ : Act Nat Nat)] ⟨[], Memories.empty, []⟩) :=
  ⟨2, _, emitMain_run a, rfl⟩

/-- Erasing the steps of `emitMain`'s traced runs gives its runs by the
emit dialect's rules alone. -/
example (fuel : Nat) :=
  Func.run_eraseSteps (d := EmitDialect) lay Empty.elim RunItems.empty emitModule emitMain .nil fuel

end FirTest.TraceDialect
