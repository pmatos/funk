import Fir.Execution.Behaviour
import Fir.Validation.Scope

/-!
# Running a function

The interpreter runs a function of a module, of any dialect (G0). It is a
monadic definitional interpreter with fuel (S7, ADR-2026-10-29-2009),
written once against an abstract monad `m`. It runs each op through its
dialect's `DialectDenote d m`, so the effects that ops need are the
dialect's constraints on `m`, and the interpreter itself needs only a
monad. It adds two effects of its own. A path that reaches a case that
validation rules out ends stuck, so it computes in `ExceptT Stuck m`. In
the set monad that is the spec's `Run`: the set of the ways a run may end,
each path with a result, with UB or stuck. And it runs the calls, the call
effect of the previous sections, since a call needs the module and the
run's fuel.

A run keeps an _environment_: the value of every name it has defined so
far. It starts with the function's parameters bound to the arguments, then
runs the entry block op by op.

* An op that is not a terminator and calls no function takes its operands
  from the environment, and its dialect's `denote` gives its results,
  which join the environment.
* An op that is not a terminator and calls a function, as its dialect's
  `callee?` says, passes its operands to the callee, which the run looks
  up in the module by its symbol. The values that the callee returns are
  its results.
* A terminator's `exit` says where control goes. On `ret` the run returns
  the terminator's operands, any number of them (ADR-2026-10-30-0816). On
  `goto i` it binds the arguments of the block that the `i`th successor
  names to the values the successor passes (H1, ADR-2026-10-29-2010), and
  runs that block.

Every op takes one step of fuel, the terminator and the call included. A
run with no fuel left before an op ends with `fuelExhausted`. A run gives
back the steps of fuel it leaves when it returns. A callee runs with the
steps that its caller has left after the call's own step, and the caller
goes on with the steps the callee gives back, so the caller and all its
callees share one budget (ADR-2026-11-02-0836). The fuel is the
interpreter's argument, and each run gives back at most the steps it was
given (`Func.runOps_left_le`), so every run ends, however deep its calls
go: a run that recurses without end runs out of fuel.

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
* a call names a function of the module, passes one value of the right type
  for each of its parameters, and receives values of its own result types,
  which the dialect's own validation rule must ask, as the core rule for
  `call` does;
* an op owns no region: no op of M0 has one, and how regions run is left to
  H6, so validation rejects them;
* the function has an entry block, which declares no arguments.

Two checks hold a dialect's `exit` to the rules that validation makes of
its terminators. A terminator's `exit` may say `goto i` only for a
successor `i` that the terminator has, and validation fixes only how many
it has. A terminator may return only values of the function's result
types, which the dialect's own rule must ask, as the core rule for `ret`
does. So `NeverStuck` for `br` and `cond_br` needs their `exit` to name
only successors they have, which #19 proves of each: `Core.br_goto_lt` and
`Core.condBr_goto_lt`. One more condition is no check of its own: a
terminator that jumps gives no results. The interpreter binds none for it,
while validation puts them in scope in the blocks that its block
dominates, so a use of one would be stuck. No core terminator has results.
Whether validation should rule them out for every dialect is an open
question (#89).

These checks are not all of validation. The interpreter checks that a value
is defined, not that its definition dominates its use, and it checks no
other rule of validation than those above. So a run of a function that
validation rejects may end with an outcome, which means nothing: only a
valid function's runs mean something (ADR-2026-10-30-1856). No path of a
valid function's run is stuck. That is proved for every valid function
that calls no function and whose terminators meet the three conditions
above (`Func.Local`), jumps and loops included, so for every valid core
function without a `call` op; #20 extends it to calls (see "Fuel and
progress").

The interpreter's own steps never drop a path. Each step goes on, ends the
path with a result, or ends it stuck; the only computations that branch are
the ops', which the interpreter lifts into `ExceptT Stuck m` whole. A path
is lost only where an op has no outcome, which each op's totality
obligation, `OpTotal`, rules out.

Effects belong to the dialect, so the interpreter does not change when a
dialect needs a new one. `freeze`'s rule calls `choose`, and the divisions'
rules and `cond_br`'s call `ub`, so the core dialect's semantics asks for
`MonadChoice m` and `MonadUB m`, and `fir-ref`'s exhaustive and scripted
modes run this interpreter in the tree of choices, which has both. The call
effect is the one exception, and it is written once here for every
dialect: a dialect says only which of its ops call which function
(`DialectCall`). No core op calls one until #20 names the callee of `call`,
and the interpreter does not change then.
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

variable [DialectSignature d] [DialectCall d] {m : Type → Type} [Monad m] [DialectDenote d m]

/-- The function of the module `M` whose symbol is `s`. -/
def Module.func? (M : Module d) (s : Name) : Option (Func d) :=
  M.funcs.find? (·.name == s)

/-- Where a run of the function `f` on the arguments `args` starts: the ops
of its entry block, in an environment that binds each parameter to its
argument. -/
def Func.enter (f : Func d) (args : List (DVal d)) :
    Except Stuck (List (Operation d) × Env d) := do
  let some entry := f.blocks.head? | stuck "the function has no blocks"
  if !entry.params.isEmpty then stuck s!"the entry block ^{entry.label} declares arguments"
  if args.map (·.1) = f.params.map (·.2) then pure (entry.body, (f.params.map (·.1)).zip args)
  else stuck s!"a call passes @{f.name} arguments of types other than its parameter types"

/--
Runs the ops `os` of a block of the function `f`, then the blocks that
control goes to, in the environment `env`, with `n` steps of fuel left. It
returns the values that `f` returns, each with its type, and the steps of
fuel it leaves. A call runs the function of the module `M` that it names.

The callee of a call gets the `n` steps that the call leaves, and gives
back `k` of them. The caller goes on with `min k n` steps, which is `k`
(`Func.runOps_left_le`): the minimum only shows Lean that the budget
shrinks, so that the recursion ends.
-/
def Func.runOps (M : Module d) : Nat → Func d → Env d → List (Operation d) →
    ExceptT Stuck m (Result (List (DVal d) × Nat))
  | 0, _, _, _ => pure .fuelExhausted
  | _ + 1, _, _, [] => liftExcept (stuck "a block ends without a terminator")
  | n + 1, f, env, o :: os => do
    if !o.regions.isEmpty then liftExcept (stuck "an op owns a region, and no rule runs one")
    let args ← liftExcept (env.operands (sig o.op) o.operands)
    if isTerminator o.op then
      if !os.isEmpty then liftExcept (stuck "an op follows the terminator of its block")
      match ← ExceptT.lift (DialectDenote.exit o.op args) with
      | .ret =>
        if sig o.op = f.results then pure (.ret (args.toDVals, n))
        else liftExcept (stuck "the function returns values of types other than its result types")
      | .goto i =>
        let (b, env') ← liftExcept (f.jump env o.succs i)
        Func.runOps M n f env' b.body
    else match callee? o.op with
      | none =>
        let rs ← ExceptT.lift (DialectDenote.denote o.op args)
        let env' ← liftExcept (env.bind (o.results.map (·.1)) rs.toDVals
          "an op names a number of results other than it gives")
        Func.runOps M n f env' os
      | some s =>
        let some g := M.func? s | liftExcept (stuck s!"@{s} is not a function of the module")
        let (body, genv) ← liftExcept (g.enter args.toDVals)
        match ← Func.runOps M n g genv body with
        | .fuelExhausted => pure .fuelExhausted
        | .ret (vs, k) =>
          if vs.map (·.1) = returnTypes o.op then
            let env' ← liftExcept (env.bind (o.results.map (·.1)) vs
              "an op names a number of results other than it gives")
            Func.runOps M (min k n) f env' os
          else liftExcept (stuck s!"@{s} returns values of types other than its call's result types")
termination_by n _ _ _ => n
decreasing_by
  all_goals first
    | exact Nat.lt_succ_self _
    | exact Nat.lt_succ_of_le (Nat.min_le_right _ _)

/--
The run of the function `f` of the module `M` on arguments of its parameter
types, with `fuel` steps of fuel: the entry block's ops, in an environment
that holds the parameters. It returns the values that `f` returns; the
steps it leaves matter only to a caller.
-/
def Func.run (M : Module d) (f : Func d) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) : ExceptT Stuck m (Result (List (DVal d))) := do
  let (body, env) ← liftExcept (f.enter args.toDVals)
  match ← Func.runOps M fuel f env body with
  | .ret (vs, _) => pure (.ret vs)
  | .fuelExhausted => pure .fuelExhausted

/-- In the set monad, the run of a function is the spec's `Run`, whose
observation is the list of the values it returns. -/
example [DialectDenote d SetM] (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) : Run (List (DVal d)) :=
  f.run M (m := SetM) args fuel

end Fir
