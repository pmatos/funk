import VersoManual
import Fir.Execution.Jumps
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on progress with jumps and loops, which
renders `Fir.Execution.Jumps` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Progress with jumps and loops: readable blocks" =>

:::moduleDocs (fingerprint := "2246578784609202284")
:::

:::readable Fir.Env.mapM_value_ok (pin := Fir.Env.value) (pin := Fir.Env.Holds) (fingerprint := "13566937332335085816")
*Theorem: the values of names that an environment holds are found, with
their types.* If the environment $`E` holds the names
$`x_1, \dots, x_k` for the function $`f`, then looking each of them up in
$`E` in turn succeeds, with typed values $`w_1, \dots, w_k`, and
$`\mathrm{type}_f(x_i)` is the type of $`w_i` for each $`i`.

$`E`
{ref "The-fir-specification--Execution--The-environment-of-a-run"}[holds]
a name when it binds it to a value of the type that $`f` gives it, and
looking a name up gives the value of its latest binding, or is stuck when
there is none. A jump looks up the values that its successor passes this
way.
:::

:::readable Fir.Func.op_ready_of_scoped (pin := Fir.Func.runOps) (fingerprint := "13108684191324668844")
*Theorem: what a run needs of an op, from the values in scope.* Let $`f`
be {ref "The-fir-specification--Validation--The-general-rules"}[valid] in
a module context, $`b` a block of $`\mathrm{blocks}(f)`, and $`o` the op
at index $`i` of $`b`, for $`i` less than the number of ops of $`b`. If
the environment $`E`
{ref "The-fir-specification--Execution--Scope-along-a-run"}[holds every value in scope]
at $`o`, $`\mathrm{scoped}_f(E, \mathrm{label}(b), i)`, then:

* $`o` owns no region of the core's kind;
* looking the operands of $`o` up in $`E`, for the operand types
  $`\mathrm{sig}(o)`, succeeds;
* the results of $`o` are declared with the types $`\mathrm{ret}(o)`;
* if $`o` is a terminator, no op of $`b` follows it;
* if $`o` is not a terminator, an op of $`b` follows it.

These are what the
{ref "The-fir-specification--Execution--The-interpreter"}[interpreter]
checks before and after it runs an op, as for the entry block of a
function that runs straight. Here $`\mathrm{sig}(o)` and
$`\mathrm{ret}(o)` are the operand and result types of the op instance of
$`o`, as its
{ref "The-fir-specification--Abstract-syntax--Dialects"}[signature] says.
:::

:::readable Fir.Func.scoped_next (fingerprint := "12511371047988863075")
*Theorem: after an op binds its results, the environment holds every
value in scope at the next op.* Let $`f` be valid in a module context,
$`b` a block of $`\mathrm{blocks}(f)`, and $`o` the op at index $`i` of
$`b`, for $`i` less than the number of ops of $`b`. Let
$`\mathrm{scoped}_f(E, \mathrm{label}(b), i)`, let the results
$`y_1, \dots, y_k` of $`o` be declared with the types $`\mathrm{ret}(o)`,
and let $`r_1, \dots, r_k` be values of the types $`\mathrm{ret}(o)`.
Then the environment
$`E' = [y_1 \mapsto r_1, \dots, y_k \mapsto r_k] \cdot E`, each $`r_j`
with its type, holds every value in scope at the next op:

$$`\mathrm{scoped}_f(E', \mathrm{label}(b), i + 1)`

This is how the invariant goes from one op to the next.
:::

:::readable Fir.Func.jump_ok (pin := Fir.Func.jump) (fingerprint := "5130593395890871916")
*Theorem: from an environment that holds every value in scope, a jump
from a terminator with no results to a successor it has succeeds, and
lands holding every value in scope at its target.* Let $`f` be valid in a module
context, $`b` a block of $`\mathrm{blocks}(f)`, and $`o` the op at index
$`i` of $`b`, for $`i` less than the number of ops of $`b`, and let:

* $`\mathrm{scoped}_f(E, \mathrm{label}(b), i)`;
* $`o` be a terminator;
* $`o` have no result types: $`\mathrm{ret}(o)` is empty;
* $`k` be less than $`\mathrm{nsucc}(o)`, the number of successors of the
  op instance of $`o`.

Then the jump from $`o` to its successor $`k` in $`E` succeeds: it goes
to a block $`b'` of $`\mathrm{blocks}(f)`, in an environment $`E'` with
$`\mathrm{scoped}_f(E', \mathrm{label}(b'), 0)`.

The jump takes the successor $`k` of $`o`, finds the block
$`b' = \mathrm{block}_f(l)` that its label $`l` names, looks up in $`E`
the values that it passes, binds the arguments of $`b'` to them in front
of $`E`, and checks that their types are the types of the arguments. It
is stuck when a step fails. Validation makes every step succeed, and the
values in scope at the first op of $`b'` are its arguments, just bound,
or were in scope at $`o`.
:::

:::readable Fir.Func.Local (fingerprint := "9965686972155161032")
*Definition: a function that runs within itself.* The ops of a function
$`f` _run within $`f`_ when, for every op $`o` of every block of $`f`:

* $`o` calls no function: $`\mathrm{callee}(o)` is none;
* if $`o` is a terminator, whenever $`\mathrm{exit}_o` may end with
  $`\mathsf{goto}~i`, on any operands, $`i < \mathrm{nsucc}(o)`, and $`o`
  has no result types;
* if $`o` is a terminator, whenever $`\mathrm{exit}_o` may end with
  $`\mathsf{ret}`, on any operands, its operand types are the result types
  of $`f`.

$`\mathrm{callee}(o)` and $`\mathrm{exit}_o`, run in the set monad, are
what the dialect
{ref "The-fir-specification--Execution--Effects-and-op-semantics"}[says of the op].
A jump goes only to a successor that the terminator has, and the
interpreter binds no result of a terminator. Validation fixes how many
successors a terminator has, not which one its exit picks, and does not
rule out results of a terminator for every dialect: in M0 that is the
dialect's obligation (ADR-2026-11-02-2248), and no core terminator has
any. Here, and in the blocks below, the dialect is one that the
interpreter can run in the set monad, as for
{ref "The-fir-specification--Execution--The-runs-of-a-function___-and-fuel-monotonicity"}[the runs of a function].
:::

:::readable Fir.Func.Straight.local (pin := Fir.Func.Straight) (fingerprint := "16264839822882521456")
*Theorem: a function that runs straight runs within itself.* A function
whose ops
{ref "The-fir-specification--Execution--Progress-and-no-stuck-path"}[run straight]
calls no function, never jumps, and returns only values of its result
types, so it meets the three conditions above. So these theorems extend
those of the section on progress and no stuck path.
:::

:::readable Fir.exit_of_lift (fingerprint := "83627928794343671")
*Lemma: an exit, made a step of the run, goes where the exit goes.* If
$`\mathrm{exit}_o(v^*)`, made a computation of the run, may end with the
place to go $`x`, then $`\mathrm{exit}_o(v^*)` may end with $`x`. It turns a
step of the run back into a fact about the op's exit.
:::

:::readable Fir.Func.local_noStuck Fir.Func.local_hasPath (pin := Fir.NoStuck) (pin := Fir.HasPath) (fingerprint := "15034650218610630385")
*Theorem: from any op of any block on, the run of a function that runs
within itself has no stuck path, and has a path when its ops are total.*
Let $`f` be valid in a module context and run within itself, and take any
module $`M`, budget $`n`, block $`b` of $`\mathrm{blocks}(f)`, index $`i`
less than the number of ops of $`b`, and environment $`E` with
$`\mathrm{scoped}_f(E, \mathrm{label}(b), i)`. Let $`o^*` be the ops of
$`b` from index $`i` on. Then:

* $`\mathrm{run}_M(n, f, E, o^*)` has no stuck path: it may not end stuck;
* if every op of every block of $`f` is
  {ref "The-fir-specification--Execution--Poison-classes"}[total], it has a
  path: it may end in some way.

Here $`\mathrm{run}_M(n, f, E, o^*)` is the
{ref "The-fir-specification--Execution--The-interpreter"}[interpreter]'s
run of the ops $`o^*` of $`f`, in the set monad, in the environment
$`E`, with $`n` steps of fuel. The proof is by induction on $`n`. An op
is ready, its results bind and the invariant holds at the next op; a
return returns values of the right types; and a jump lands at the first
op of its target with the invariant, with one step less.
:::

:::readable Fir.Func.neverStuck_of_local Fir.Func.progress_of_local (pin := Fir.NeverStuck) (pin := Fir.Progress) (fingerprint := "4083108106508352031")
*Theorem: a valid function that runs within itself has no stuck path, and
has progress when its ops are total, jumps and loops included.* Let $`f`
be valid in a module context and run within itself. For every module
$`M` and every vector $`v^*` of values of its parameter types, let
$`R = \mathrm{runs}_M(f)(v^*)`:

* $`R` has
  {ref "The-fir-specification--Execution--Fuel-and-progress"}[no stuck path]:
  at every budget $`n`, no path of $`R_n` is stuck;
* if every op of every block of $`f` is total, $`R` has
  {ref "The-fir-specification--Execution--Fuel-and-progress"}[progress]: at
  every budget $`n`, $`R_n` has some outcome.

Here $`\mathrm{runs}_M(f)(v^*)_n` is the
{ref "The-fir-specification--Execution--The-runs-of-a-function___-and-fuel-monotonicity"}[run of f]
on $`v^*` with $`n` steps of fuel. A run may jump to any block, as often
as its fuel allows. Every valid core function without a
$`\mathsf{call}` op meets the hypotheses, as the section on
{ref "The-fir-specification--Execution--Core-functions-without-calls"}[core functions without calls]
shows.
:::
