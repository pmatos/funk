import Fir.Execution.Behaviour
import Fir.Validation.Scope

/-!
# Running a function

The interpreter runs a function of any dialect (G0). It is a monadic
definitional interpreter with fuel (S7, ADR-2026-10-29-2009), written once
against an abstract monad `m`. It runs each op through its dialect's
`DialectDenote d m`, so the effects that ops need are the dialect's
constraints on `m`, and the interpreter itself needs only a monad. It adds
one effect of its own: a path that reaches a case that validation rules out
ends stuck, so it computes in `ExceptT Stuck m`. In the set monad that is
the spec's `Run`: the set of the ways a run may end, each path with a
result, with UB or stuck.

A run keeps an _environment_: the value of every name it has defined so
far. It starts with the function's parameters bound to the arguments, then
runs the entry block op by op.

* An op that is not a terminator takes its operands from the environment,
  and its dialect's `denote` gives its results, which join the environment.
* A terminator's `exit` says where control goes. On `ret` the run returns
  the terminator's operands, any number of them (ADR-2026-10-30-0816). On
  `goto i` it binds the arguments of the block that the `i`th successor
  names to the values the successor passes (H1, ADR-2026-10-29-2010), and
  runs that block.

Every op takes one step of fuel, the terminator included. A run with no
fuel left before an op ends with `fuelExhausted`, so every run ends.

The interpreter checks what it needs in order to take each step, and a few
more rules of validation. A path that fails a check is stuck, with a reason
for people. Validation makes each of these checks of a valid function:

* an operand is defined, and defined before the op runs, as the scope rule
  `Func.InScope` asks;
* an operand's value has the op's operand type, as `Func.OpValid` asks of
  the operand types;
* an op has as many operands as its op instance takes and as many results
  as it gives;
* a block ends with a terminator, and nothing follows its terminator;
* a successor names a block of the function, and passes one value of the
  right type for each of that block's arguments;
* an op owns no region: no op of M0 has one, and how regions run is left to
  H6, so validation rejects them;
* the function has an entry block, which declares no arguments.

Two checks hold a dialect's `exit` to the rules that validation makes of
its terminators. A terminator's `exit` may say `goto i` only for a
successor `i` that the terminator has, and validation fixes only how many
it has. A terminator may return only values of the function's result
types, which the dialect's own rule must ask, as the core rule for `ret`
does. So `NeverStuck` for `br` and `cond_br` (#19) needs their `exit` to
name only successors they have.

These checks are not all of validation. The interpreter checks that a value
is defined, not that its definition dominates its use, and it checks no
other rule of validation than those above. So a run of a function that
validation rejects may end with an outcome, which means nothing: only a
valid function's runs mean something (ADR-2026-10-30-1856). No path of a valid function's run is stuck, which
ticket #10 proves for its tracer subset (see "Fuel and progress").

The interpreter's own steps never drop a path. Each step goes on, ends the
path with a result, or ends it stuck; the only computations that branch are
the ops', which the interpreter lifts into `ExceptT Stuck m` whole. A path
is lost only where an op has no outcome, which each op's totality
obligation, `OpTotal`, rules out.

Effects belong to the dialect, so the interpreter does not change when a
dialect needs a new one. `freeze`'s rule calls `choose` and the divisions'
rules call `ub`, so the core dialect's semantics asks for `MonadChoice m`
and `MonadUB m`, and `fir-ref`'s exhaustive and scripted modes run this
interpreter in the tree of choices, which has both.
A call needs the module, which `denote` cannot reach, so #20 gives `call` a
call effect, and all calls share the run's fuel budget. That budget is an
argument of this interpreter, which `denote` neither sees nor returns, so a
call effect cannot yet charge its callee's steps to the caller's budget.
Sharing it changes how the interpreter counts fuel; that design is open
(#20).
-/

namespace Fir

/-- The values of a vector, each with its type. -/
def HVector.toDVals {Ty : Type} [TyDenote Ty] : {ts : List Ty} → HVector toType ts →
    List ((t : Ty) × ⟦t⟧)
  | [], .nil => []
  | t :: _, .cons v vs => ⟨t, v⟩ :: HVector.toDVals vs

variable {d : Dialect} [TyDenote d.Ty]

/-- The values a run has defined, by name, the latest first. -/
abbrev Env (d : Dialect) [TyDenote d.Ty] := List (Name × DVal d)

/-- A path that is stuck, for a reason. -/
def stuck (reason : String) : Except Stuck α := .error ⟨reason⟩

/-- The value of the name `x`: its latest definition. -/
def Env.value (env : Env d) (x : Name) : Except Stuck (DVal d) :=
  match env.lookup x with
  | some v => pure v
  | none => stuck s!"%{x} is not defined"

/-- Binds names to values, one each, or is stuck for `why`. -/
def Env.bind (env : Env d) (names : List Name) (vs : List (DVal d)) (why : String) :
    Except Stuck (Env d) :=
  if names.length = vs.length then pure (names.zip vs ++ env) else stuck why

variable [DecidableEq d.Ty]

/-- The values of the names `xs`, one for each type of `ts`. -/
def Env.operands (env : Env d) : (ts : List d.Ty) → List Name → Except Stuck (HVector toType ts)
  | [], [] => pure .nil
  | t :: ts, x :: xs => do
    let ⟨t', v⟩ ← env.value x
    if h : t' = t then pure (.cons (h ▸ v) (← env.operands ts xs))
    else stuck s!"%{x} does not have the operand's type"
  | _, _ => stuck "an op has a number of operands other than its op instance takes"

/-- The block that control goes to on `goto i` from a terminator with
successors `succs`, with its arguments bound to the values that the `i`th
successor passes. -/
def Func.jump (f : Func d) (env : Env d) (succs : List Succ) (i : Nat) :
    Except Stuck (Block d × Env d) := do
  let some s := succs[i]? | stuck s!"the terminator has no successor {i}"
  let some b := f.block? s.label | stuck s!"^{s.label} is not a block of the function"
  let vs ← s.args.mapM env.value
  let env' ← env.bind (b.params.map (·.1)) vs
    s!"^{s.label} takes a number of arguments other than its successor passes"
  if vs.map (·.1) = b.params.map (·.2) then pure (b, env')
  else stuck s!"^{s.label} takes arguments of types other than its successor passes"

variable [DialectSignature d] {m : Type → Type} [Monad m] [DialectDenote d m]

/--
Runs the ops `os` of a block of the function `f`, then the blocks that
control goes to, in the environment `env`, with `n` steps of fuel left. It
returns the values that the function returns, each with its type.
-/
def Func.runOps (f : Func d) : Nat → Env d → List (Operation d) →
    ExceptT Stuck m (Result (List (DVal d)))
  | 0, _, _ => pure .fuelExhausted
  | _ + 1, _, [] => liftExcept (stuck "a block ends without a terminator")
  | n + 1, env, o :: os => do
    if !o.regions.isEmpty then liftExcept (stuck "an op owns a region, and no rule runs one")
    let args ← liftExcept (env.operands (sig o.op) o.operands)
    if isTerminator o.op then
      if !os.isEmpty then liftExcept (stuck "an op follows the terminator of its block")
      match ← ExceptT.lift (DialectDenote.exit o.op args) with
      | .ret =>
        if sig o.op = f.results then pure (.ret args.toDVals)
        else liftExcept (stuck "the function returns values of types other than its result types")
      | .goto i =>
        let (b, env') ← liftExcept (f.jump env o.succs i)
        f.runOps n env' b.body
    else
      let rs ← ExceptT.lift (DialectDenote.denote o.op args)
      let env' ← liftExcept (env.bind (o.results.map (·.1)) rs.toDVals
        "an op names a number of results other than it gives")
      f.runOps n env' os

/--
The run of the function `f` on arguments of its parameter types, with `fuel`
steps of fuel: the entry block's ops, in an environment that holds the
parameters. `args` has one value for each parameter, so each parameter is
bound.
-/
def Func.run (f : Func d) (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    ExceptT Stuck m (Result (List (DVal d))) := do
  let some entry := f.blocks.head? | liftExcept (stuck "the function has no blocks")
  if !entry.params.isEmpty then
    liftExcept (stuck s!"the entry block ^{entry.label} declares arguments")
  f.runOps fuel ((f.params.map (·.1)).zip args.toDVals) entry.body

/-- In the set monad, the run of a function is the spec's `Run`, whose
observation is the list of the values it returns. -/
example [DialectDenote d SetM] (f : Func d) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) : Run (List (DVal d)) :=
  f.run (m := SetM) args fuel

end Fir
