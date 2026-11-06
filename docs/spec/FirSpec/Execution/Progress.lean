import VersoManual
import Fir.Execution.Progress
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on progress and no stuck path, which
renders `Fir.Execution.Progress` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "Progress and no stuck path: readable blocks" =>

:::readable Fir.eq_cons_of_head? (fingerprint := "10406841056930139947")
*Lemma: a list with a first element is that element followed by the
rest.* The proofs below use it to name the blocks of a function that come
after its entry block.
:::

:::readable Fir.Func.defs_entry (fingerprint := "9808104181613512877")
*Theorem: a function's definitions start with its parameters, then its
entry block's arguments and the results of its entry block's ops.* Let
$`e` be the first block of the function $`f`, with the ops
$`o_1, \dots, o_m`. Then, for some list $`D` of further definitions,

$$`\begin{aligned} \mathrm{defs}(f) = {} & \mathrm{params}(f) \cdot \mathrm{args}(e) \\ & \cdot \mathrm{results}(o_1) \cdots \mathrm{results}(o_m) \\ & \cdot D \end{aligned}`

Here $`\mathrm{defs}(f)` is the
{ref "The-fir-specification--Validation--Scope-and-symbols"}[definitions]
of $`f`, $`\mathrm{params}(f)` its parameters, $`\mathrm{args}(e)` the
arguments that $`e` declares and $`\mathrm{results}(o)` the results of
the op $`o`, each with its type, and $`\cdot` puts lists one after the
other. Validation makes the names of $`\mathrm{defs}(f)` distinct, so the
results of each op of the entry block are new names.
:::

:::readable Fir.Func.defsBefore (fingerprint := "4619211757213957648")
*Definition: what the entry block has defined before an op.* For a
function $`f`, a block $`e` with the ops $`o_0, o_1, \dots` and an index
$`i`, $`\mathrm{before}_f(e, i)` is the parameters of $`f`, then the
results of the ops of $`e` before index $`i`, each with its type:

$$`\begin{aligned} \mathrm{before}_f(e, i) = {} & \mathrm{params}(f) \cdot \mathrm{results}(o_0) \\ & \cdots \mathrm{results}(o_{i-1}) \end{aligned}`

with every op of $`e` when $`i` is past its end. A function that runs
straight, below, runs only its entry block, which declares no arguments,
so these are the names its run has bound before the op at index $`i`.
:::

:::readable Fir.Func.mem_defsBefore (fingerprint := "7194390988467382235")
*Theorem: in a valid function, a value in scope at an op of the entry
block was defined before it.* Let $`f` be
{ref "The-fir-specification--Validation--The-general-rules"}[valid] in a
module context, and $`e` its entry block, which declares no arguments.
If the value $`x` is
{ref "The-fir-specification--Validation--Dominance"}[in scope] at the op
at index $`i` of $`e`, $`\mathrm{inscope}_f(x, \mathrm{label}(e), i)`,
then $`x` is a name of $`\mathrm{before}_f(e, i)`.

No block dominates the entry block but itself, so the only definitions
that dominate a use there are the parameters and the results of the ops
before it.
:::

:::readable Fir.Func.results_fresh (fingerprint := "2726647588056703228")
*Theorem: the results of an op of the entry block are definitions of the
function, and new.* Let $`f` be valid in a module context, $`e` its entry
block, which declares no arguments, and $`o` the op at index $`i` of
$`e`, for $`i` less than the number of ops of $`e`. Then:

* $`f` gives each result $`y : t` of $`o` its type:
  $`\mathrm{type}_f(y) = t`;
* no name of $`\mathrm{before}_f(e, i)` is the name of a result of $`o`.

So when the run binds the results of $`o`, they have the types that
$`f` gives them, and they hide no name that the run bound before.
:::

:::readable Fir.Func.holds_next (pin := Fir.Env.Holds) (fingerprint := "472778959504751451")
*Theorem: after an op of the entry block binds its results, the
environment holds what was defined before the next op.* Let $`f` be valid
in a module context, $`e` its entry block, which declares no arguments,
and $`o` the op at index $`i` of $`e`, for $`i` less than the number of
ops of $`e`. Let the environment $`E` hold the names of
$`\mathrm{before}_f(e, i)`, let the results $`y_1, \dots, y_k` of $`o` be
declared with the types $`\mathrm{ret}(o)`, and let $`r_1, \dots, r_k` be
values of the types $`\mathrm{ret}(o)`. Then the environment

$$`[y_1 \mapsto r_1, \dots, y_k \mapsto r_k] \cdot E`

holds the names of $`\mathrm{before}_f(e, i + 1)`, each $`r_j` with its
type. An environment
{ref "The-fir-specification--Execution--The-environment-of-a-run"}[holds]
a name when it binds it to a value of the type that $`f` gives it, and
$`\mathrm{ret}(o)` is the result types of the op instance of $`o`, as its
{ref "The-fir-specification--Abstract-syntax--Dialects"}[signature] says.
:::

:::readable Fir.Func.op_ready (pin := Fir.Func.runOps) (fingerprint := "17657522360999363202")
*Theorem: what a run needs of an op of the entry block.* Let $`f` be valid
in a module context, $`e` its entry block, which declares no arguments,
and $`o` the op at index $`i` of $`e`, for $`i` less than the number of
ops of $`e`. If the environment $`E` holds the names of
$`\mathrm{before}_f(e, i)`, then:

* $`o` owns no region;
* looking the operands of $`o` up in $`E`, for the operand types
  $`\mathrm{sig}(o)`, succeeds;
* the results of $`o` are declared with the types $`\mathrm{ret}(o)`;
* if $`o` is a terminator, no op of $`e` follows it;
* if $`o` is not a terminator, an op of $`e` follows it.

These are what the
{ref "The-fir-specification--Execution--The-interpreter"}[interpreter]
checks before and after it runs an op: a region, which no rule runs, an
operand that is not bound or has the wrong type, a count of results
other than the op gives, an op after a terminator, or a block that ends
without one, each makes the path stuck. Here $`\mathrm{sig}(o)` is the
operand types of the op instance of $`o`.
:::

:::readable Fir.Func.Straight (fingerprint := "17264026091780647438")
*Definition: a function that runs straight.* The ops of a function $`f`
_run straight_ to a return when, for every op $`o` of every block of
$`f`:

* $`o` calls no function: $`\mathrm{callee}(o)` is none;
* the exit of $`o` never says $`\mathsf{goto}~i`: on no operands and for
  no $`i` may $`\mathrm{exit}_o`, run in the set monad, end with
  $`\mathsf{goto}~i`;
* if $`o` is a terminator, its operand types are the result types of
  $`f`.

$`\mathrm{callee}(o)` and $`\mathrm{exit}_o` are what the dialect
{ref "The-fir-specification--Execution--Effects-and-op-semantics"}[says of the op]:
the function it calls, and where control goes when it ends a block. Such
a function runs only its entry block, which keeps the proof simple. A
valid function whose ops are those of the roadmap's tracer bullet,
$`\mathsf{const}`, $`\mathsf{add}` without flags and $`\mathsf{ret}`,
runs straight. The
{ref "The-fir-specification--Execution--Progress-with-jumps-and-loops"}[jumps and loops]
and the
{ref "The-fir-specification--Execution--Progress-with-calls"}[calls] come
in later sections.
:::

:::readable Fir.Func.straight_noStuck Fir.Func.straight_hasPath (pin := Fir.NoStuck) (pin := Fir.HasPath) (fingerprint := "7188831905626722678")
*Theorem: from any op of its entry block on, the run of a function that
runs straight has no stuck path, and has a path when its ops are total.*
Let $`f` be valid in a module context and run straight, let $`e` be its
entry block, which declares no arguments, and take any module $`M`,
budget $`n`, index $`i` less than the number of ops of $`e`, and
environment $`E` that holds the names of $`\mathrm{before}_f(e, i)`. Let
$`o^*` be the ops of $`e` from index $`i` on. Then:

* $`\mathrm{run}_M(n, f, E, o^*)` has no stuck path: it may not end stuck;
* if every op of every block of $`f` is
  {ref "The-fir-specification--Execution--Poison-classes"}[total], it has a
  path: it may end in some way.

Here $`\mathrm{run}_M(n, f, E, o^*)` is the
{ref "The-fir-specification--Execution--The-interpreter"}[interpreter]'s
run of the ops $`o^*` of $`f`, in the set monad, in the environment
$`E`, with $`n` steps of fuel. The proof is by induction on $`n`, op by
op: each op is ready, its results bind and the next op holds what was
defined before it, and the terminator returns.
:::

:::readable Fir.Func.enter_entry (pin := Fir.Func.enter) (fingerprint := "2252482915170068968")
*Theorem: a run starts at the entry block.* Let $`e` be the first block
of the function $`f`, which declares no arguments, and let
$`v_1, \dots, v_n` be values of the types $`t_1, \dots, t_n` of the
parameters $`p_1, \dots, p_n` of $`f`. Then entering $`f` with them
starts at the ops of $`e`, with each parameter bound to its value:

$$`\mathrm{enter}_f(v_1, \dots, v_n) = \mathsf{ok}\bigl(\mathrm{body}(e),\ E\bigr)`

where

$$`\begin{aligned} E = [ & p_1 \mapsto (t_1, v_1), \\ & \dots, p_n \mapsto (t_n, v_n)] \end{aligned}`

Here $`\mathrm{enter}_f` takes the first block of $`f`, is stuck when
there is none, when it declares arguments or when the values do not have
the parameter types, and otherwise starts there.
:::

:::readable Fir.Func.holds_params (pin := Fir.Env.Holds) (fingerprint := "10281406635602267665")
*Theorem: before the first op, a run holds the parameters.* Let $`f` be
valid in a module context, and $`v_1, \dots, v_n` values of the types
$`t_1, \dots, t_n` of its parameters $`p_1, \dots, p_n`. For every block
$`e`, the environment
$`[p_1 \mapsto (t_1, v_1), \dots, p_n \mapsto (t_n, v_n)]` holds the names
of $`\mathrm{before}_f(e, 0)`, which are the parameters: it binds each to
a value of the type that $`f` gives it. With the previous theorem, this
is where the induction of the next one starts.
:::

:::readable Fir.Func.neverStuck Fir.Func.progress (pin := Fir.NeverStuck) (pin := Fir.Progress) (fingerprint := "3729878795102707803")
*Theorem: a valid function that runs straight has no stuck path, and has
progress when its ops are total.* Let $`f` be valid in a module context
and run straight. For every module $`M` and every vector $`v^*` of values
of its parameter types, let $`R = \mathrm{runs}_M(f)(v^*)`:

* $`R` has
  {ref "The-fir-specification--Execution--Fuel-and-progress"}[no stuck path]:
  at every budget $`n`, no path of $`R_n` is stuck;
* if every op of every block of $`f` is total, $`R` has
  {ref "The-fir-specification--Execution--Fuel-and-progress"}[progress]: at
  every budget $`n`, $`R_n` has some outcome.

Here $`\mathrm{runs}_M(f)(v^*)_n` is the
{ref "The-fir-specification--Execution--The-runs-of-a-function___-and-fuel-monotonicity"}[run of f]
on $`v^*` with $`n` steps of fuel. Such a function calls no function, so
neither $`M` nor the context it is valid in plays a part. Every valid
function whose ops are those of the tracer bullet, $`\mathsf{const}`,
$`\mathsf{add}` without flags and $`\mathsf{ret}`, meets the hypotheses,
as the section on
{ref "The-fir-specification--Execution--The-runs-of-core-functions"}[the runs of core functions]
shows.
:::
