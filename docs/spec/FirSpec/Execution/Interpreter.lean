import VersoManual
import Fir.Execution.Interpreter
import Fir.Validation.Rules
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the interpreter, which renders
`Fir.Execution.Interpreter` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The interpreter: readable blocks" =>

:::moduleDocs (fingerprint := "3251824520712610684")
:::

:::readable Fir.HVector.toDVals (pin := Fir.DVal) (fingerprint := "11457153560144753281")
*Definition: the typed values of a vector.* For values $`v_1, \dots, v_n`
of the types $`t_1, \dots, t_n`, the list of pairs
$`(t_1, v_1), \dots, (t_n, v_n)`: each value with its type. An op's
semantics takes and gives values of the types that its
{ref "The-fir-specification--Abstract-syntax--Dialects"}[signature] fixes,
while an environment and a return hold typed values; this turns the one
into the other.
:::

:::readable Fir.Env Fir.stuck Fir.Env.value Fir.Env.bind (pin := Fir.Stuck) (pin := Fir.DVal) (pin := Fir.Func.Valid) (fingerprint := "15837783068621949683")
*Definition: environments, being stuck, looking a name up and binding
names.* An _environment_ $`E` is a list of the values a run has defined,
each a name with a typed value, $`x \mapsto (t, v)`, the latest first.

* A path that is _stuck_ ends with a reason, text for people that says
  which check failed. The reasons below write names as the text format
  does, such as `%x` and `^l`.
* $`E(x)`, the value of the name $`x`, is the value of the first pair for
  $`x` in $`E`: its latest definition. When $`E` has none, the path is
  stuck: "`%x` is not defined".
* Binding the names $`x_1, \dots, x_n` to the typed values
  $`w_1, \dots, w_k` gives, when $`n = k`, the environment
  $`[x_1 \mapsto w_1, \dots, x_n \mapsto w_n] \cdot E`: the new pairs in
  front of $`E`. When $`n \neq k`, the path is stuck, with a reason that
  the caller gives.

A {ref "The-fir-specification--Validation--The-general-rules"}[valid function]
defines each name once, so its latest definition is its only one along a
path. The latest first matters for loops: a block that
runs again binds its arguments and results again, and the new values hide
the old ones. Being
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[stuck]
is how the interpreter ends a path that validation rules out.
:::

:::readable Fir.Env.operands (pin := Fir.Env.value) (fingerprint := "4784251075266048821")
*Definition: the operands of an op.* For the operand types
$`t_1, \dots, t_n` of an op and the names $`x_1, \dots, x_k` of its
operands, the values of the operands in an environment $`E` are
$`(v_1, \dots, v_n)` when $`k = n` and each $`E(x_i)` is a value $`v_i` of
type $`t_i`. The names are looked up from the first, and the first check
that fails makes the path stuck:

* "`%x` is not defined", when $`E` has no value for $`x_i`;
* "`%x` does not have the operand's type", when its type is not $`t_i`;
* "an op has a number of operands other than its op instance takes", when
  one list ends before the other.

So an op's semantics only ever sees values of the types that its signature
promises.
:::

:::readable Fir.Func.jump (pin := Fir.Func.block?) (pin := Fir.Succ) (pin := Fir.Env.value) (pin := Fir.Env.bind) (fingerprint := "7857999587418638399")
*Definition: jumping to a successor.* Let a terminator of the function
$`f` have the
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[successors]
$`s_0, \dots, s_{m-1}`, and let its
{ref "The-fir-specification--Execution--Effects-and-op-semantics"}[rule]
say $`\mathsf{goto}~i`. In the environment $`E`, the jump finds where the run
goes on, by these steps; the first that fails makes the path stuck, with
the reason in brackets:

1. Take $`s_i` (there is no successor $`i` when $`i \geq m`). Its label is
   $`l` and the names of the values it passes are $`y_1, \dots, y_k`.
2. Take the block $`b = \mathrm{block}_f(l)` (no block of $`f` has the
   label $`l`).
3. Look up $`w_j = E(y_j)` for each $`j` (some $`y_j` is not defined).
4. Bind the names $`z_1, \dots, z_p` of the arguments of $`b` to
   $`w_1, \dots, w_k` (the counts differ).
5. Check that the types of $`w_1, \dots, w_k` are the types of the
   arguments of $`b` (they differ).

The run goes on at the ops of $`b`, in the environment
$`[z_1 \mapsto w_1, \dots, z_p \mapsto w_p] \cdot E`. Here
$`\mathrm{block}_f(l)` is the first block of $`f` with the label $`l`, as in
{ref "The-fir-specification--Validation--Scope-and-symbols"}[scope and symbols].
This is how block arguments take the values that a branch passes
(ADR-2026-10-29-2010), and a poison value arrives as poison.
:::

:::readable Fir.Module.func? (pin := Fir.Module.funcs) (pin := Fir.Module.Valid) (fingerprint := "3654794366578574978")
*Definition: the function with a symbol.* $`\mathrm{lookup}_M(s)` is the
first function of the module $`M`, in the order of its items, whose symbol
is $`s`, or none when there is no such function. A call of $`s` runs it.
Validation gives each function of a
{ref "The-fir-specification--Validation--The-general-rules"}[valid module]
its own symbol, so there the first is the only one.
:::

:::readable Fir.Func.enter (pin := Fir.Func.blocks) (fingerprint := "7467722205350593985")
*Definition: entering a function.* $`\mathrm{enter}_f(w_1, \dots, w_n)`,
for typed values $`w_1, \dots, w_n` and a function $`f` with the
parameters $`(p_1 : t_1), \dots, (p_m : t_m)`, finds where a run of $`f`
starts, by these steps; the first that fails makes the path stuck:

1. Take the entry block $`e`, the first block of $`f` (the function has no
   blocks).
2. Check that $`e` declares no arguments (the entry block declares
   arguments).
3. Check that the types of $`w_1, \dots, w_n` are $`t_1, \dots, t_m`
   (a call passes arguments of other types).

The run starts at the ops of $`e`, in the environment
$`[p_1 \mapsto w_1, \dots, p_m \mapsto w_m]`, which holds the parameters
and nothing else.
:::

:::readable Fir.Func.runOps (pin := Fir.Result) (pin := Fir.Exit) (pin := Fir.Stuck) (pin := Fir.Env.operands) (pin := Fir.Env.bind) (pin := Fir.Func.jump) (pin := Fir.Module.func?) (pin := Fir.Func.enter) (fingerprint := "16914946586688321552")
*Definition: running the ops of a block.* For every dialect, for every way
of computing in which the dialect's ops have their
{ref "The-fir-specification--Execution--Effects-and-op-semantics"}[semantics],
$`\mathrm{run}_M(n, f, E, o^*)` runs the ops $`o^*` of a block of the
function $`f` of the module $`M`, then the blocks that control goes to, in
the environment $`E`, with $`n` steps of fuel. It ends in one of four ways:
it returns typed values with some steps of fuel left; it runs out of
{ref "The-fir-specification--Execution--Fuel-and-progress"}[fuel]; it is
stuck; or an op's semantics ends it, for example with immediate UB.

With no fuel, $`\mathrm{run}_M(0, f, E, o^*)` runs out of fuel. With
$`n + 1` steps, a block with no ops left is stuck ("a block ends without a
terminator"). Otherwise the run takes the first op $`o` of $`o^*`, leaves
the rest $`o'^*`, takes one step of fuel, and goes on by these steps; a
check that fails makes the path stuck:

1. Check that $`o` owns no region; no rule runs one.
2. Take $`v^*`, the values of the operands of $`o` in $`E`, for the
   operand types of $`o`.
3. When $`o` is a terminator, check that $`o'^*` is empty, then run
   $`\mathrm{exit}_o(v^*)`:
   * on $`\mathsf{ret}`, check that the operand types of $`o` are the
     result types of $`f`, and return $`v^*`, each value with its type,
     with $`n` steps left;
   * on $`\mathsf{goto}~i`, jump to the successor $`i` of $`o`, and run the
     ops of the block it names, in the environment the jump gives, with
     $`n` steps.
4. When $`o` is not a terminator and $`\mathrm{callee}(o)` is none, run
   $`\mathrm{denote}_o(v^*)`, bind the names of the results of $`o` to the
   values it gives (their counts must agree), and run $`o'^*` with $`n`
   steps.
5. When $`o` is not a terminator and $`\mathrm{callee}(o)` is the symbol
   $`s`, take
   $`g = \mathrm{lookup}_M(s)` (stuck when no function of $`M` has the
   symbol $`s`), enter $`g` with $`v^*`, and run its entry
   block with $`n` steps:
   * when the callee runs out of fuel, so does the caller;
   * when it returns typed values with $`k` steps left, check that their
     types are the result types of $`o`, bind the names of the results of
     $`o` to them (their counts must agree), and run $`o'^*` with
     $`\min(k, n)` steps.

Here $`\mathrm{exit}_o`, $`\mathrm{denote}_o` and $`\mathrm{callee}(o)`
are what the dialect says of $`o`; looking operands up, jumping, looking a
symbol up and entering a function are the blocks above. Each op takes one
step, the terminator and the call included, and a callee runs on the steps
its caller has left, so a caller and all its callees share one budget
(ADR-2026-11-02-0836). A run gives back at most the steps it was given, as
{ref "The-fir-specification--Execution--The-runs-of-a-function___-and-fuel-monotonicity"}[the runs of a function]
shows, so $`\min(k, n)` is $`k`; the minimum makes it plain that the
budget shrinks at every step, so that every run ends, however deep its
calls go. When the callee is stuck or ends with UB, so does the caller.
:::

:::readable Fir.Func.run (pin := Fir.Run) (pin := Fir.Func.enter) (pin := Fir.Func.runOps) (fingerprint := "7652563225295482938")
*Definition: the run of a function.* For a function $`f` of the module
$`M`, values $`v^*` of its parameter types and $`\mathit{fuel}` steps of
fuel, the run enters $`f` with $`v^*`, and runs its entry block with
$`\mathit{fuel}` steps. A return gives the values returned, each with its
type, and drops the steps left, which matter only to a caller; running
out of fuel stays so, and a path that is stuck or ends with UB stays so.

In the
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[set monad],
this run is a run in the sense of the outcomes: the set of the ways it
may end, each with the list of values returned, out of fuel, with UB or
stuck.
:::
