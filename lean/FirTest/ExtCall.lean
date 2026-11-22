import FirTest.Run
import FirTest.TraceDialect

/-!
Tests of the external-call rule (#239, the human's rulings Q1 and Q2 of
2026-11-21): which declarations accept a call, exactly or as a variadic
prefix; `fir-ref run` on a call to a declaration, which is UB in the layers
with no world, and stuck when no declaration of the call's types names the
symbol; and, in the traced layer, a toy dialect whose external-call rule
shows an event, through which a call to a declaration takes one step and
the run goes on with the rule's results.
-/

namespace FirTest.ExtCall

open Fir Fir.Memory FirRef FirTest FirTest.TraceDialect

/-! # A declaration accepts a call -/

/-- `extern @g(%a: i32) -> i8`. -/
def exactG : Extern CoreDialect := { name := "g", params := [("a", .int 32)], results := [.int 8] }

/-- `extern @g(%a: i32, ...) -> i8`. -/
def variadicG : Extern CoreDialect := { exactG with variadic := true }

#guard exactG.accepts [.int 32] [.int 8]
#guard !exactG.accepts [.int 32, .int 64] [.int 8]
#guard !exactG.accepts [] [.int 8]
#guard !exactG.accepts [.int 64] [.int 8]
#guard !exactG.accepts [.int 32] [.int 16]
#guard !exactG.accepts [.int 32] []
#guard variadicG.accepts [.int 32] [.int 8]
#guard variadicG.accepts [.int 32, .int 64, .ptr 0] [.int 8]
#guard !variadicG.accepts [] [.int 8]
#guard !variadicG.accepts [.int 64, .int 32] [.int 8]
#guard !variadicG.accepts [.int 32, .int 64] [.int 16]

/-- A module whose one item is `extern @g(%a: i32) -> i8`. -/
def declModule : Module CoreDialect := { items := [.extern exactG], locs := [] }

#guard declModule.declares "g" [.int 32] [.int 8]
#guard !declModule.declares "h" [.int 32] [.int 8]
#guard !declModule.declares "g" [.int 64] [.int 8]
#guard !declModule.declares "g" [.int 32] [.int 8, .int 8]

/-! # `fir-ref run` on a call to a declaration -/

/-- `@f(%a: i32) -> i32` calls `@g`, declared as `extern @g` then `decl`, on
`%a`, for an `i32`. -/
def callsG (decl : String) : String :=
  oneFunc ("extern @g" ++ decl ++ " {\n}\n\nfunc @f(%a: i32) -> i32 {\n^e:\n" ++
    "  %r: i32 = call @g %a @0\n  ret %r @0\n}\n")

/-- The report of a run that hits the UB of an external call. -/
def extUB : RunReport :=
  { out := "{\"kind\":\"ub\",\"reason\":\"" ++ extCallUB ++ "\",\"choices\":0}", status := 0 }

-- A declaration that accepts the call: the call is UB, a layer with no world.
#guard runText (callsG "(%a: i32) -> i32") "@f" ["1"] == extUB
#guard runText (callsG "(...) -> i32") "@f" ["1"] == extUB
#guard runText (callsG "(%a: i32, ...) -> i32") "@f" ["poison"] == extUB
-- With a world given, `fir-ref run --world` sees the same UB.
#guard (runBytes "t.fir" (callsG "(%a: i32) -> i32").toUTF8 defaultFuel "@f" ["1"]
  (world := some [])).out.startsWith ("{\"kind\":\"ub\",\"reason\":\"" ++ extCallUB ++ "\"")
-- A declaration of other types, and no declaration: the call is stuck.
#guard runText (callsG "(%a: i64) -> i32") "@f" ["1"] ==
  stuckBy "@g is not a function or a declaration of the call's types"
#guard runText (callsG "(%a: i32) -> i64") "@f" ["1"] ==
  stuckBy "@g is not a function or a declaration of the call's types"
#guard runText (callsG "(%a: i32, %b: i32) -> i32") "@f" ["1"] ==
  stuckBy "@g is not a function or a declaration of the call's types"
#guard runText (callsG "(%a: i32, %b: i32, ...) -> i32") "@f" ["1"] ==
  stuckBy "@g is not a function or a declaration of the call's types"
#guard runText
  (oneFunc "func @f(%a: i32) -> i32 {\n^e:\n  %r: i32 = call @g %a @0\n  ret %r @0\n}\n")
  "@f" ["1"] == stuckBy "@g is not a function or a declaration of the call's types"

/-! # A call to a declaration in the traced layer -/

/-- The ops of a toy dialect whose external calls show an event: `call @g`
calls `@g`, and `ret` returns nothing. -/
inductive XOp where
  | call (sym : Name)
  | ret
  deriving DecidableEq

/-- A dialect, for these tests, whose external-call rule shows an event. -/
abbrev XDialect : Dialect := ⟨XOp, Core.Ty⟩

instance : DialectSignature XDialect where
  sig _ := []
  returnTypes _ := []
  isTerminator
    | .ret => true
    | _ => false
  succCount _ := 0

instance : DialectCall XDialect := ⟨fun | .call s => some s | _ => none⟩

/-- The toy dialect has no memory. -/
instance : DialectEffects XDialect :=
  ⟨Empty, fun _ => .exception, fun
    | .ret => { control := true }
    | _ => {}, fun _ => none⟩

/-- An external call shows the event `7`, takes any answer, and gives no
result. -/
instance : DialectTrace XDialect where
  Event := Nat
  Answer := Nat
  IsRefinedBy := Eq
  traceAt _ _ _ :=
    { denote := fun _ _ => MonadUB.ub "no op of the toy dialect runs by its own rule"
      exit := fun
        | .ret, _ => pure .ret
        | _, _ => MonadUB.ub "not a terminator"
      extCall := fun _ _ _ => (fun (_ : Nat) => []) <$> MonadEvent.emit (7 : Nat) }

/-- The traced semantics of the toy dialect. -/
abbrev xsem := DialectTrace.traceAt (d := XDialect) lay Empty.elim RunItems.empty

/-- `call @puts`. -/
def callPuts : Operation XDialect :=
  { results := [], op := .call "puts", operands := [], succs := [], regions := [], loc := 0 }

/-- `ret`. -/
def retOp : Operation XDialect :=
  { results := [], op := .ret, operands := [], succs := [], regions := [], loc := 0 }

/-- A function that calls `@puts`, then returns. -/
def xMain : Func XDialect where
  name := "main"
  params := []
  results := []
  body := { blocks := [{ label := "entry", params := [], body := [callPuts, retOp] }] }

/-- A module that declares `@puts`, with no function of that symbol. -/
def xModule : Module XDialect :=
  { items := [.extern { name := "puts", params := [], results := [] }, .func xMain],
    locs := [(0, .unknown)] }

#guard xModule.declares "puts" [] []
#guard !xModule.declares "puts" [] [.int 8]
#guard (xModule.func? "puts").isNone

/-- The external-call rule shows the event `7` with any answer, keeps the
traced state, and gives no result. -/
theorem extCall_run (a : Nat) (s : TraceState Unit (unitsOf lay)) :
    xsem.extCall "puts" [] [] s (.ok ([], [⟨(7 : Nat), a⟩], s)) := by
  show ((fun (_ : Nat) => ([] : List (DVal XDialect))) <$> MonadEvent.emit (7 : Nat) :
    TraceM (DialectTrace.Acts XDialect) (TraceState Unit (unitsOf lay)) _) s _
  rw [map_eq_pure_bind, TraceM.bind_apply]
  exact .inl ⟨a, [⟨(7 : Nat), a⟩], s, _, ⟨a, rfl⟩, rfl, by simp [TraceEnd.after]⟩

/-- The call to the declaration `@puts` takes one step, shows the world its
event with any answer, and the run goes on with the step left: `ret`
returns, with no step left over. -/
theorem xMain_ops (a : Nat) (s : TraceState Unit (unitsOf lay)) :
    letI := xsem
    Func.traceOps (DialectTrace.Acts XDialect) xModule 2 xMain [] [callPuts, retOp] s
      (.ok (.ok (.ret ([], 0)), [⟨(7 : Nat), a⟩], s)) := by
  letI := xsem
  have hp : Func.TStepPath (B := DialectTrace.Acts XDialect) xModule 0 xMain [] retOp [] s
      (.ok (.ok (.ret ((HVector.nil : HVector toType (sig (d := XDialect) XOp.ret)).toDVals, 0)),
        [], s)) :=
    .ret rfl rfl rfl rfl rfl rfl
  have hret : Func.traceOps (DialectTrace.Acts XDialect) xModule 1 xMain [] [retOp] s
      (.ok (.ok (.ret ([], 0)), [], s)) :=
    (Func.tStepPath_iff (TraceEnd.notStuck_ok _ _ _)).2 hp
  have h := (Func.tStepPath_iff (TraceEnd.notStuck_ok _ _ _)).2
    (Func.TStepPath.ext (o := callPuts) (os := [retOp]) (args := .nil) (vs := [])
      rfl rfl rfl rfl (by decide) (by decide) (extCall_run a s) rfl rfl hret)
  simpa [TraceEnd.after] using h

end FirTest.ExtCall
