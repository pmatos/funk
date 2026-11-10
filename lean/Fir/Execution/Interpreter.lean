import Fir.Execution.Behaviour
import Fir.Validation.Scope

/-!
# Running a function

The interpreter runs a function of a module, of any dialect: it is written
once, for every dialect (ADR-2026-10-29-2016). It is a definitional
interpreter with fuel (ADR-2026-10-29-2009): a recursive function that
follows the program op by op, and counts its steps against a budget. It
runs each op by the semantics that its dialect gives it, in whatever way
of computing provides the effects that the dialect needs, such as choosing
bits or immediate UB. It adds two effects of its own: a path can be stuck,
when it reaches a case that validation rules out, and an op can call a
function of the module. In the set of the ways a run may end, a run of the
interpreter is a run in the sense of the outcomes: each path ends with a
result, with UB, stuck, or out of fuel.

A run keeps an _environment_: the value of every name it has defined so
far. It starts with the function's parameters bound to the arguments, and
runs the entry block op by op:

* A terminator says where control goes. On `ret` the run returns the
  terminator's operands, any number of them (ADR-2026-10-30-0816). On a
  jump to a successor, it binds the arguments of the block that the
  successor names to the values that the successor passes
  (ADR-2026-10-29-2010), and runs that block.
* The interpreter runs only regions of the core's kind: a function's body.
  An op that owns regions of a dialect's kinds runs by its dialect's
  semantics, like any other op, and the interpreter does not enter them.
  What such a region means is its dialect's to say, through the semantics
  of the op instance.
* An op that is not a terminator and calls no function takes its operands
  from the environment, and its dialect's semantics gives its results,
  which join the environment.
* An op that is not a terminator and calls a function, as its dialect
  says, passes its operands to the callee, which the run looks up in the
  module by its symbol. The values that the callee returns are its
  results.

Every op takes one step of fuel, the terminator and the call included. A
run with no fuel left before an op runs out of fuel. A callee runs on the
steps that its caller has left, and gives back the steps it leaves, so the
caller and all its callees share one budget (ADR-2026-11-02-0836). A run
gives back at most the steps it was given, so every run ends, however deep
its calls go: a run that recurses without end runs out of fuel.

The interpreter checks what it needs in order to take each step, and a
path that fails a check is stuck, with a reason for people. Validation
makes each of these checks of a valid function:

* an operand is defined before the op runs, as the scope rule asks;
* an operand's value has the op's operand type, and an op has as many
  operands as its op instance takes and as many results as it gives;
* a successor names a block of the function, and passes one value of the
  right type for each of that block's arguments;
* a call names a function of the module, which the dialect's own
  validation rule must ask, as the core rule for `call` does;
* the function has an entry block, which declares no arguments;
* a call passes one value of the right type for each of its callee's
  parameters, and receives values of its own result types, which the
  dialect's own validation rule must ask, as the core rule for `call`
  does;
* an op owns no region of the core's kind: a region inside an op would be
  structured control flow, which is not designed, so validation asks that
  the kind of each region of an op be a dialect's;
* a block ends with a terminator, and nothing follows its terminator.

Two checks hold a dialect's terminators to the rules that validation
makes of them. A terminator's rule may jump only to a successor that the
terminator has, while validation fixes only how many it has; the branch
obligations prove it of `br` and `cond_br`. And a terminator may return
only values of the function's result types, which the dialect's own rule
must ask, as the core rule for `ret` does. One more condition is no check
of its own: a terminator that jumps gives no results. The interpreter
binds none for it, while validation puts them in scope in the blocks that
its block dominates, so a use of one would be stuck. No core terminator
has results. That condition is the dialect's obligation, not a rule of
validation, until exceptions and unwinding are designed
(ADR-2026-11-02-2248).

These checks are not all of validation. The interpreter checks that a
value is defined, not that its definition dominates its use. So a run of a
function that validation rejects may end with an outcome, which means
nothing: only a valid function's runs mean something (ADR-2026-10-30-1856).
No path of a valid function's run is stuck. That is proved for every
function of a module whose functions are all valid, meet the conditions
above on their terminators, and call only functions of the module, of the
types of their calls: jumps, loops, calls and recursion included, so for
every function of every valid core module (see the sections on progress).

The interpreter's own steps never drop a path. Each step goes on, ends the
path with a result, or ends it stuck; only an op's semantics can branch.
A path is lost only where an op has no outcome, which the totality
obligation rules out for every op that the interpreter runs by its own
rule: a terminator, or an op that calls no function. An op that calls a
function runs its callee, never its own semantics.

Effects belong to the dialect, so the interpreter does not change when a
dialect needs a new one. The core dialect's `freeze` chooses bits, and its
divisions and `cond_br` may end with immediate UB, so `fir-ref`'s
exhaustive, scripted and sampled modes run this interpreter in a tree of
choices, which has both effects. The call effect is the one exception,
and it is written once here for every dialect: a dialect says only which
of its ops call which function. In the core dialect, `call @g` calls `@g`.
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
    if o.ownsCoreRegion then
      liftExcept (stuck "an op owns a region of the core's kind, and no rule runs one")
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

/-!
A check made when the spec is built: in the set of the ways a run may end,
the run of a function is a run in the sense of the outcomes, whose
observation is the list of the values it returns.
-/

example [DialectDenote d SetM] (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) : Run (List (DVal d)) :=
  f.run M (m := SetM) args fuel

end Fir
