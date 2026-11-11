import VersoManual
import Fir.Execution.Monotone
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the runs of a function and fuel
monotonicity, which renders `Fir.Execution.Monotone`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "The runs of a function, and fuel monotonicity: readable blocks" =>

:::moduleDocs (fingerprint := "15385580192323226087")
:::

:::readable Fir.Func.runs (pin := Fir.Func.run) (fingerprint := "2702186033688374399")
*Definition: the runs of a function.* Let $`f` be a function and $`M` a
module, of a dialect that the interpreter can run in the set monad: its
types have values and a test of equality, and its ops have a
{ref "The-fir-specification--Abstract-syntax--Dialects"}[signature], say
which function they call, and have a
{ref "The-fir-specification--Execution--Effects-and-op-semantics"}[semantics]
in the set monad. Every block of this section is about such a dialect.

The runs of $`f` in $`M` give, for each vector $`v^*` of values of the
parameter types of $`f` and each budget $`n`, the run
$`\mathrm{runs}_M(f)(v^*)_n` of the
{ref "The-fir-specification--Execution--The-interpreter"}[interpreter]: it
enters $`f` with $`v^*`, runs its entry block with $`n` steps of fuel, and
keeps the values of a return, dropping the steps left. It is a set of
the ways the run may end: with the list of the typed values that $`f`
returns, out of fuel, with UB, or stuck.

These are
{ref "The-fir-specification--Execution--Refinement"}[runs of a function]
in the sense of refinement, and their observable behaviour on $`v^*` is
what $`f` does on $`v^*`.
:::

:::readable Fir.LeavesAtMost (fingerprint := "12085131045341374937")
*Definition: a computation that leaves at most $`n` steps.* A run of the
ops of a block, when it returns, ends with the values $`a` it returns and
the steps of fuel $`k` it leaves: the result $`\mathsf{ret}~(a, k)`. A
computation $`x` of such results _leaves at most $`n` steps_ when each of
its returns leaves at most $`n`:

$$`\begin{aligned} & \mathrm{leaves}_{\le n}(x) \\ \iff\ & \forall a, k.\ x \leadsto \mathsf{ret}~(a, k) \implies k \le n \end{aligned}`

Here $`x \leadsto r` says that $`x` may end with the result $`r`
({ref "The-fir-specification--Execution--Reading-a-run-path-by-path"}[reading a run path by path]).
A callee gives its caller back the steps it leaves, and the caller goes on
with the smaller of those and its own; this bound shows that the callee
never gives back more than it got.
:::

:::readable Fir.LeavesAtMost.bind Fir.LeavesAtMost.of_stuck Fir.LeavesAtMost.exhausted Fir.LeavesAtMost.ret Fir.LeavesAtMost.mono (fingerprint := "16058696819039482584")
*Theorem: leaving at most $`n` steps, piece by piece.* For every budget
$`n`:

* $`x \mathbin{>\!\!>\!\!=} g` leaves at most $`n` steps when $`g\,b` does
  for every result $`b` that $`x` may end with.
* A check that is stuck, for any reason, leaves at most $`n` steps: it
  returns nothing.
* $`\{\mathsf{ok}~\mathsf{fuel\_exhausted}\}`, a run out of fuel, leaves
  at most $`n` steps: it returns nothing.
* $`\{\mathsf{ok}~(\mathsf{ret}~(a, k))\}` leaves at most $`n` steps when
  $`k \le n`.
* A computation that leaves at most $`n` steps leaves at most $`n'` steps,
  for every $`n' \ge n`.

These are the pieces from which the interpreter builds a run of ops, so
the bound can be followed through a run step by step.
:::

:::readable Fir.Func.runOps_left_le (pin := Fir.Func.runOps) (fingerprint := "15531259396566572660")
*Theorem: a run gives back at most the fuel it was given.* For every module
$`M`, budget $`n`, function $`f`, environment $`E` and list of ops
$`o^*`, the run $`\mathrm{run}_M(n, f, E, o^*)` leaves at most $`n` steps.

Here $`\mathrm{run}_M(n, f, E, o^*)` is the interpreter's run, in the set
monad, of the ops $`o^*` of a block of $`f`, then of the blocks that
control goes to, in the environment $`E`, with $`n` steps of fuel. Each op
takes one step; a return leaves the steps that remain; a call runs its
callee with the steps that remain, and goes on with the smaller of the
callee's leftover $`k` and those steps.

It holds whatever the ops do, by induction on $`n`: a callee runs with
fewer steps than its caller had, so it gives back at most those. So the
smaller of the two is always $`k`, and a caller goes on with exactly the
steps its callee leaves. The proof of fuel monotonicity, below, needs
that.
:::

:::readable Fir.Ahead (fingerprint := "12995770293673452999")
*Definition: one computation ahead of another by $`j` steps.* Let $`x` and
$`y` be computations whose returns carry the steps they leave. $`y` is
_ahead of $`x` by $`j` steps_, as a run with $`j` more steps of fuel
should be, when for all $`a`, $`k` and $`r`:

* every return of $`x` is a return of $`y` that leaves $`j` more steps;
* every UB of $`x` is a UB of $`y`;
* every return of $`y` that leaves $`k` steps is a return of $`x` that
  leaves $`k - j` steps, with $`j \le k`, unless $`x` may run out of fuel;
* every UB of $`y` is a UB of $`x`, unless $`x` may run out of fuel.

$$`x \leadsto \mathsf{ret}~(a, k) \implies y \leadsto \mathsf{ret}~(a, k + j)`

$$`\mathsf{ub}~r \in x \implies \mathsf{ub}~r \in y`

$$`\begin{aligned} & y \leadsto \mathsf{ret}~(a, k) \\ \implies\ & \bigl(j \le k \,\wedge\, x \leadsto \mathsf{ret}~(a, k - j)\bigr) \\ \vee\ & x \leadsto \mathsf{fuel\_exhausted} \end{aligned}`

$$`\begin{aligned} \mathsf{ub}~r \in y \implies\ & \mathsf{ub}~r \in x \\ \vee\ & x \leadsto \mathsf{fuel\_exhausted} \end{aligned}`

This is
{ref "The-fir-specification--Execution--Fuel-and-progress"}[fuel monotonicity]
for a run of ops, with the steps left kept track of, so that it carries
through a call: a callee with $`j` more steps gives back $`j` more, and its
caller goes on with $`j` more. Stuck paths play no part.
:::

:::readable Fir.Ahead.bind Fir.Ahead.bindRun Fir.Ahead.of_stuck Fir.Ahead.exhausted Fir.Ahead.ret (fingerprint := "17705216673644351520")
*Theorem: being ahead by $`j` steps, piece by piece.* For every $`j`:

* $`x \mathbin{>\!\!>\!\!=} h` is ahead of $`x \mathbin{>\!\!>\!\!=} g` by $`j`
  steps when $`h\,b` is ahead of $`g\,b` by $`j` steps for every result
  $`b` that $`x` may end with.
* A call. Let $`y` be ahead of $`x` by $`j` steps, and let $`x` leave at
  most $`n` steps. Let $`g` and $`h` both give
  $`\{\mathsf{ok}~\mathsf{fuel\_exhausted}\}` on the result
  $`\mathsf{fuel\_exhausted}`, and, for every $`b` and every $`k \le n`,
  let $`h(\mathsf{ret}~(b, k + j))` be ahead of $`g(\mathsf{ret}~(b, k))`
  by $`j` steps. Then $`y \mathbin{>\!\!>\!\!=} h` is ahead of
  $`x \mathbin{>\!\!>\!\!=} g` by $`j` steps.
* A check that is stuck for a reason $`s` is ahead of itself by $`j`
  steps.
* Every computation is ahead of $`\{\mathsf{ok}~\mathsf{fuel\_exhausted}\}`
  by $`j` steps.
* $`\{\mathsf{ok}~(\mathsf{ret}~(a, k + j))\}` is ahead of
  $`\{\mathsf{ok}~(\mathsf{ret}~(a, k))\}` by $`j` steps.

In the second, $`x` and $`y` are a callee's runs with fewer and with more
fuel, and $`g` and $`h` what the caller does with the callee's result: a
callee out of fuel ends its caller so, and a return that leaves $`j` more
steps lets the caller go on with $`j` more.
:::

:::readable Fir.Func.runOps_ahead (pin := Fir.Func.runOps) (fingerprint := "10316076547955429506")
*Theorem: a run with $`j` more steps of fuel is ahead by $`j` steps.* For
every module $`M`, budget $`n`, number $`j`, function $`f`, environment
$`E` and list of ops $`o^*`, the run $`\mathrm{run}_M(n + j, f, E, o^*)`
is ahead of $`\mathrm{run}_M(n, f, E, o^*)` by $`j` steps. Here
$`\mathrm{run}_M` is the interpreter's run of a block's ops, in the set
monad, as above: each op takes one step, and a call goes on with the
steps its callee leaves.

It holds for every function, calls included, whatever the ops do, by
induction on $`n`. With no fuel, the smaller run runs out of fuel, and
everything is ahead of that. Otherwise both runs take the same step: an
op never sees the fuel. A callee run with $`j` more steps gives back
$`j` more, so its caller goes on with $`j` more.
:::

:::readable Fir.Ev.dropLeft (fingerprint := "12592833793426350993")
*Definition: an end without the steps left.* A run of ops ends with
$`\mathsf{ok}~(\mathsf{ret}~(a, k))`, $`\mathsf{ok}~\mathsf{fuel\_exhausted}`,
$`\mathsf{stuck}~s` or $`\mathsf{ub}~r`. The run of a function ends the
same ways, but its return carries only the values. $`\mathrm{drop}(e)`
forgets the steps left of a return and keeps every other end as it is:

$$`\mathrm{drop}(\mathsf{ok}~(\mathsf{ret}~(a, k))) = \mathsf{ok}~(\mathsf{ret}~a)`

The steps left matter only to a caller.
:::

:::readable Fir.Func.run_run (pin := Fir.Func.enter) (fingerprint := "11166300857095917995")
*Theorem: a function's run ends as its entry block's ops end, or stuck
where it cannot start.* For every module $`M`, function $`f`, vector
$`v^*` of values of its parameter types, budget $`n` and end $`e`,
$`e` is an end of $`\mathrm{runs}_M(f)(v^*)_n` exactly when one of these
holds:

* for some ops $`o^*` and environment $`E`, entering $`f` with $`v^*`
  starts at the ops $`o^*` in the environment $`E`, and
  $`e = \mathrm{drop}(e')` for an end $`e'` of
  $`\mathrm{run}_M(n, f, E, o^*)`;
* for some reason $`s`, entering $`f` with $`v^*` is stuck for $`s`, and
  $`e = \mathsf{stuck}~s`.

$$`\begin{aligned} & e \in \mathrm{runs}_M(f)(v^*)_n \\ \iff\ & \bigl(\exists o^*, E.\ \mathrm{enter}_f(v^*) = \mathsf{ok}(o^*, E) \\ & \quad \wedge\, \exists e' \in \mathrm{run}_M(n, f, E, o^*). \\ & \qquad e = \mathrm{drop}(e')\bigr) \\ \vee\ & \bigl(\exists s.\ \mathrm{enter}_f(v^*) = \mathsf{stuck}~s \\ & \quad \wedge\, e = \mathsf{stuck}~s\bigr) \end{aligned}`

Here $`\mathrm{enter}_f(v^*)` is where the run of $`f` on the values
$`v^*`, with their types, starts: the ops of its entry block, in the
environment that binds each parameter to its value, or stuck when the
function has no blocks, its entry block declares arguments, or the values
do not have its parameter types. With this theorem, what is proved of
runs of ops carries over to runs of functions.
:::

:::readable Fir.Func.run_up Fir.Func.run_down (fingerprint := "7091037276741261556")
*Theorem: with more fuel, a function's run keeps each return and UB, and
gains none unless the smaller run may run out of fuel.* For every module
$`M`, function $`f`, vector $`v^*` of values of its parameter types,
budget $`n` and number $`j`, let $`e` be an end that is neither out of
fuel nor stuck: a return or UB.

* Up: if $`e \in \mathrm{runs}_M(f)(v^*)_n`, then
  $`e \in \mathrm{runs}_M(f)(v^*)_{n + j}`.
* Down: if $`e \in \mathrm{runs}_M(f)(v^*)_{n + j}`, then
  $`e \in \mathrm{runs}_M(f)(v^*)_n`, or
  $`\mathrm{runs}_M(f)(v^*)_n \leadsto \mathsf{fuel\_exhausted}`.

They follow from the run of the entry block's ops with $`j` more steps
being ahead by $`j` steps, through the theorem above.
:::

:::readable Fir.Func.fuelMonotone (pin := Fir.FuelMonotone) (fingerprint := "13061949907589445450")
*Theorem: the runs of every function are fuel-monotone.* For every module
$`M`, every function $`f` and every vector $`v^*` of values of the
parameter types of $`f`, the run $`R = \mathrm{runs}_M(f)(v^*)` is
{ref "The-fir-specification--Execution--Fuel-and-progress"}[fuel-monotone]:
for all budgets $`n \le m` and every outcome $`t` other than
$`\mathsf{fuel\_exhausted}`,

$$`t \in \mathrm{out}(R_n) \implies t \in \mathrm{out}(R_m)`

$$`\begin{aligned} & t \in \mathrm{out}(R_m) \\ \implies\ & t \in \mathrm{out}(R_n) \\ \vee\ & \mathsf{fuel\_exhausted} \in \mathrm{out}(R_n) \end{aligned}`

This is the first of the three obligations, and it needs no hypothesis:
not validity, and nothing of the ops, calls and recursion included. Only
the interpreter counts fuel, an op never sees it, and a callee gives
back to its caller the steps it leaves (ADR-2026-11-02-0836). For a
function that reaches an op with no execution rule, it holds only
vacuously on the paths that reach that op (ADR-2026-10-30-1855).
:::
