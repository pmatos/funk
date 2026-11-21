import FirTest.TraceDialect

/-!
A toy dialect with calls, for the tests of divergence across a replaced callee
(ADR-2026-11-09-1540, stage 3c-2 of #233). Its op `emit` shows the event `0`
to the world and gets any answer, `skip` does nothing, `call @g` calls the
function `@g`, `br` jumps back to the function's first block, `ret`
returns, and `ub` hits UB. Its ops are monotone in the traced layer and have finitely many
outcomes, given the world's answers, so the traced layer's theorems apply.

The module `callModule` has a callee `@g`, which takes a step to `skip`, then
returns, and two callers that loop forever around a call of `@g`: `@quiet`
silently, `@loud` showing an act on every round.
-/

namespace FirTest.TraceCallDialect

open Fir Fir.Memory FirTest.TraceDialect

/-- The ops of the call dialect. -/
inductive CallOp where
  | emit
  | skip
  | call (sym : Name)
  | br
  | ret
  | ub
  deriving DecidableEq

/-- A dialect, for these tests, with an event and calls. -/
abbrev CallDialect : Dialect := ⟨CallOp, Core.Ty⟩

instance : DialectSignature CallDialect where
  sig _ := []
  returnTypes _ := []
  isTerminator
    | .br | .ret => true
    | _ => false
  succCount
    | .br => 1
    | _ => 0

instance : DialectCall CallDialect := ⟨fun | .call s => some s | _ => none⟩

/-- The call dialect has no memory. -/
instance : DialectEffects CallDialect :=
  ⟨Empty, fun _ => .exception, fun
    | .br | .ret => { control := true }
    | _ => {}⟩

/-- The call dialect's events are numbers, answered by numbers: `emit` shows
`0`. -/
instance : DialectTrace CallDialect where
  Event := Nat
  Answer := Nat
  IsRefinedBy := Eq
  traceAt _ _ _ :=
    { denote := fun
        | .emit, _ => (fun (_ : Nat) => .nil) <$> MonadEvent.emit (0 : Nat)
        | .skip, _ => pure .nil
        | .call _, _ => MonadUB.ub "a call runs its callee"
        | .ub, _ => MonadUB.ub "ub"
        | .br, _ | .ret, _ => MonadUB.ub "a terminator exits"
      exit := fun
        | .br, _ => pure (.goto 0)
        | .ret, _ => pure .ret
        | _, _ => MonadUB.ub "not a terminator" }

/-- The traced state of a run of the call dialect, with no memory of its own. -/
abbrev St : Type := TraceState Unit (unitsOf lay)

/-- The traced semantics of the call dialect. -/
abbrev sem := DialectTrace.traceAt (d := CallDialect) lay Empty.elim RunItems.empty

/-! # The ops' semantics -/

/-- `emit` shows the event `0` with any answer, and keeps the traced state. -/
theorem emit_iff (args : HVector toType (sig (d := CallDialect) CallOp.emit)) (s : St)
    (e : TraceEnd (DialectTrace.Acts CallDialect) St
      (HVector toType (returnTypes (d := CallDialect) CallOp.emit))) :
    sem.denote CallOp.emit args s e ↔ ∃ n : Nat, e = .ok (.nil, [⟨(0 : Nat), n⟩], s) := by
  dsimp only [DialectDenote.denote, sem, DialectTrace.traceAt]
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

/-- Refinement of the call dialect's acts is reflexive. -/
theorem act_refl (x : DialectTrace.Acts CallDialect) : x ⊑ x :=
  Act.isRefinedBy_refl (fun _ => (rfl : _ = _)) x

/-- The call dialect's ops are monotone in its traced semantics. -/
theorem call_monotone (op : CallDialect.Op) :
    letI := sem
    OpTraceMonotone (d := CallDialect) (B := DialectTrace.Acts CallDialect) (σ := St) op := by
  letI := sem
  intro args args' _
  have ubAll : ∀ {α β : Type} {r : α → β → Prop} (m : String),
      TraceRefinedBy r (MonadUB.ub m : TraceM (DialectTrace.Acts CallDialect) St α)
        (MonadUB.ub m : TraceM (DialectTrace.Acts CallDialect) St β) :=
    fun m _ _ _ e' _ => ⟨.error (m, []), rfl, TraceEnd.Allows.of_ub _ e'⟩
  cases op with
  | emit =>
    refine ⟨fun _ s s' hs e' he' => ?_, (fun h => nomatch h)⟩
    obtain ⟨n, rfl⟩ := (emit_iff args' s' e').1 he'
    exact ⟨.ok (.nil, [⟨(0 : Nat), n⟩], s), (emit_iff args s _).2 ⟨n, rfl⟩, trivial,
      List.isRefinedBy_refl act_refl _, hs⟩
  | skip =>
    refine ⟨fun _ s s' hs e' he' => ?_, (fun h => nomatch h)⟩
    have he' : e' = .ok (.nil, [], s') := he'
    subst he'
    exact ⟨.ok (.nil, [], s), rfl, trivial, trivial, hs⟩
  | call _ => exact ⟨fun _ => ubAll _, (fun h => nomatch h)⟩
  | ub => exact ⟨fun _ => ubAll _, (fun h => nomatch h)⟩
  | br =>
    refine ⟨(fun h => nomatch h), fun _ s s' hs e' he' => ?_⟩
    have he' : e' = .ok (.goto 0, [], s') := he'
    subst he'
    exact ⟨.ok (.goto 0, [], s), rfl, rfl, trivial, hs⟩
  | ret =>
    refine ⟨(fun h => nomatch h), fun _ s s' hs e' he' => ?_⟩
    have he' : e' = .ok (.ret, [], s') := he'
    subst he'
    exact ⟨.ok (.ret, [], s), rfl, rfl, trivial, hs⟩

/-- Every function of the call dialect has its ops monotone in the traced
layer. -/
theorem traceOpsMonotone (g : Func CallDialect) :
    letI := sem
    g.TraceOpsMonotone (DialectTrace.Acts CallDialect) St :=
  fun _ _ o _ _ => call_monotone o.op

/-- The call dialect's ops have finitely many outcomes, given the world's
answers: the stream fixes the answer to `emit`. -/
theorem call_traceFinite :
    letI := sem
    OpsTraceFinite CallDialect Nat Nat St := by
  letI := sem
  intro op _ args
  have one : ∀ {α : Type} (a : α), TraceFinitelyMany (E := Nat) (Ans := Nat)
      (pure a : TraceM (DialectTrace.Acts CallDialect) St α) := fun a s _ =>
    ⟨[(a, [], s)], fun a' t s' h _ => by
      have h : (Except.ok (a', t, s') : TraceEnd (Act Nat Nat) St _) = .ok (a, [], s) := h
      cases h
      exact List.mem_singleton_self _⟩
  have none : ∀ {α : Type} (m : String), TraceFinitelyMany (E := Nat) (Ans := Nat)
      (MonadUB.ub m : TraceM (DialectTrace.Acts CallDialect) St α) :=
    fun _ _ _ => ⟨[], fun _ _ _ h _ => nomatch h⟩
  cases op with
  | emit =>
    refine ⟨fun _ s ans => ⟨(ans 0).toList.map fun n => (.nil, [⟨(0 : Nat), n⟩], s),
      fun a t s' h hag => ?_⟩, (fun h => nomatch h)⟩
    obtain ⟨n, he⟩ := (emit_iff args s _).1 h
    simp only [Except.ok.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have := hag 0 _ rfl
    exact List.mem_map.2 ⟨n, by simp [this], rfl⟩
  | skip => exact ⟨fun _ => one _, (fun h => nomatch h)⟩
  | call _ => exact ⟨fun _ => none _, (fun h => nomatch h)⟩
  | ub => exact ⟨fun _ => none _, (fun h => nomatch h)⟩
  | br => exact ⟨(fun h => nomatch h), fun _ => one _⟩
  | ret => exact ⟨(fun h => nomatch h), fun _ => one _⟩

/-! # The module -/

/-- An op of the call dialect with no operand and no result. -/
def mkOp (op : CallOp) (succs : List Succ := []) : Operation CallDialect :=
  { results := [], op := op, operands := [], succs := succs, regions := [], loc := 0 }

/-- A jump back to the block `^loop`. -/
def brLoop : Operation CallDialect := mkOp .br [Succ.mk "loop" []]

/-- The callee `@g`: a step to `skip`, then return. -/
def g : Func CallDialect where
  name := "g"
  params := []
  results := []
  body := { blocks := [{ label := "entry", params := [], body := [mkOp .skip, mkOp .ret] }] }

/-- The new body of `@g`: return at once, one step fewer. -/
def newBody : Region CallDialect :=
  { blocks := [{ label := "entry", params := [], body := [mkOp .ret] }] }

/-- A caller that calls `@g`, then jumps back, forever, showing nothing. -/
def quiet : Func CallDialect where
  name := "quiet"
  params := []
  results := []
  body := { blocks := [{ label := "loop", params := [], body := [mkOp (.call "g"), brLoop] }] }

/-- A caller that calls `@g`, then emits, then jumps back, forever. -/
def loud : Func CallDialect where
  name := "loud"
  params := []
  results := []
  body := { blocks := [Block.mk "loop" [] [mkOp (.call "g"), mkOp .emit, brLoop]] }

/-- The module of the callee and its two callers. -/
def callModule : Module CallDialect :=
  { items := [.func g, .func quiet, .func loud], locs := [(0, .unknown)] }

/-- The module with `@g`'s body replaced by the new one. -/
abbrev newModule : Module CallDialect := callModule.replaceBody g.name newBody

end FirTest.TraceCallDialect
