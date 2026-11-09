import VersoManual
import Fir.Execution.RunPaths
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the ways a step goes on, which
renders `Fir.Execution.RunPaths` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The ways a step goes on: readable blocks" =>

:::moduleDocs (fingerprint := "11491586926943817244")
:::

:::readable Fir.Ev.NotStuck (fingerprint := "8592670422160197782")
*Definition: an end that is not stuck.* A path of a run ends with a
result, with UB, or
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[stuck].
An end $`e` is _not stuck_ when $`e \neq \mathsf{stuck}~s` for every
reason $`s`. The refinement proofs of the next sections follow only such
paths: a stuck path is not an outcome, and refinement compares outcomes.
:::

:::readable Fir.run_liftExcept_bind Fir.run_lift_bind (fingerprint := "1201202150306426404")
*Theorems: two kinds of step, read path by path.* Proof plumbing, so that
the proofs below can read a run one step at a time without unfolding the
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[set monad].
Let $`g` give a computation for each value, and let $`e` be an end.

* Let $`x` be a check of the interpreter, which gives a value or is
  stuck, such as looking up an op's operands. If $`e` is not stuck, then
  $`e` is an end of $`x`, then $`g`, exactly when $`x` gives a value $`a`
  and $`e` is an end of $`g(a)`.
* Let $`s` be a computation of the set monad, which is never stuck, such
  as an op's semantics. Then $`e` is an end of $`s`, then $`g`, exactly
  when $`s` may end with a value $`a` and $`e` is an end of $`g(a)`, or
  $`s` may end with $`\mathsf{ub}~r` and $`e = \mathsf{ub}~r`.
:::

:::readable Fir.Func.StepPath Fir.Func.stepPath_iff (pin := Fir.Func.runOps) (pin := Fir.Ev.NotStuck) (fingerprint := "16985377396009429692")
*Definition and theorem: the eight ways a step goes on.* Write
$`\mathrm{run}_M(n, f, E, o^*)` for the
{ref "The-fir-specification--Execution--The-interpreter"}[run of the ops]
$`o^*` of the function $`f` of the module $`M`, in the environment $`E`,
with $`n` steps of fuel, and $`e \in \mathrm{run}_M(n, f, E, o^*)` when
one of its paths ends with $`e`. A run of ops that returns gives typed
values $`u^*` and the steps $`k` it leaves: $`\mathsf{ret}~(u^*, k)`.

Take a run $`\mathrm{run}_M(n + 1, f, E, o\,o'^*)` whose first op is $`o`.
In each of the eight ways, $`o` owns no region, and the values $`v^*` of
its operands are found in $`E`, of its operand types. When $`o` is a terminator and $`o'^*`
is empty, its exit $`\mathrm{exit}_o(v^*)` may end:

1. with $`\mathsf{ub}~r`, and the path ends with $`\mathsf{ub}~r`;
2. with a return, the operand types of $`o` are the result types of $`f`,
   and the path ends with $`\mathsf{ret}~(v^*, n)`;
3. with a jump to the successor $`i`, which goes to the block $`b` in the
   environment $`E_1`, and the path ends with an end $`e` of
   $`\mathrm{run}_M(n, f, E_1, \mathrm{body}(b))`.

When $`o` is not a terminator and has no callee, its semantics
$`\mathrm{denote}_o(v^*)` may end:

4. with $`\mathsf{ub}~r`, and the path ends with $`\mathsf{ub}~r`;
5. with results $`w^*`, as many as the names $`x^*` of the results of
   $`o`, and the path ends with an end $`e` of
   $`\mathrm{run}_M(n, f, [x^* \mapsto w^*] \cdot E, o'^*)`.

When $`o` is not a terminator and calls the symbol $`s`, the module has
the function $`g = \mathrm{lookup}_M(s)`, entering it,
$`\mathrm{enter}_g(v^*)`, starts at the ops $`p^*` in the environment
$`G`, and its run
$`\mathrm{run}_M(n, g, G, p^*)` may end:

6. with $`\mathsf{ub}~r`, and the path ends with $`\mathsf{ub}~r`;
7. with $`\mathsf{fuel\_exhausted}`, and the path ends so;
8. with $`\mathsf{ret}~(u^*, k)`, the types of $`u^*` are the result types
   of $`o`, the values $`u^*` are as many as the names $`x^*` of the
   results of $`o`, and the path ends with an end $`e` of
   $`\mathrm{run}_M(\min(k, n), f, [x^* \mapsto u^*] \cdot E, o'^*)`.

Here $`[x^* \mapsto w^*] \cdot E` binds each name to its value in front
of $`E`, and $`\mathrm{lookup}_M`, $`\mathrm{exit}_o`,
$`\mathrm{denote}_o` and $`\mathrm{enter}_g` are as in the
{ref "The-fir-specification--Execution--The-interpreter"}[interpreter],
which also says why a caller goes on with $`\min(k, n)` steps: a run
leaves at most the steps it was given, so this is $`k`.

*Theorem:* for every end $`e` that is not stuck,

$$`\begin{aligned} & e \in \mathrm{run}_M(n + 1, f, E, o\,o'^*) \\ \iff\ & \text{one of the eight ways} \\ & \text{ends with } e \end{aligned}`

The refinement proofs of the next sections compare two runs path by path,
one step at a time. This says once every case of a step, so that they need
not unfold the interpreter.
:::

:::readable Fir.Func.run_runOps_zero Fir.Func.run_runOps_nil (pin := Fir.Func.runOps) (pin := Fir.Ev.NotStuck) (fingerprint := "6158323989996524902")
*Theorems: a run with no fuel, and a block with no op left.* For every
module $`M`, function $`f`, environment $`E`, ops $`o^*` and budget $`n`:

* $`e \in \mathrm{run}_M(0, f, E, o^*) \iff e = \mathsf{fuel\_exhausted}`:
  a run with no fuel runs out of fuel, and does nothing else;
* no end that is not stuck is an end of
  $`\mathrm{run}_M(n + 1, f, E, \epsilon)`: a block with no op left, and
  so no terminator, is stuck.

With the eight ways above, these cover every run of ops.
:::

:::readable Fir.Func.runOps_exhausted_down (pin := Fir.Ahead) (fingerprint := "9825190398988431052")
*Theorem: a run that runs out of fuel runs out of fuel with fewer steps.*
For every module $`M`, budget $`n`, number of steps $`j`, function $`f`,
environment $`E` and ops $`o^*`, with
$`R_m = \mathrm{run}_M(m, f, E, o^*)` for every budget $`m`:

$$`\begin{aligned} & \mathsf{fuel\_exhausted} \in R_{n + j} \\ \implies\ & \mathsf{fuel\_exhausted} \in R_n \end{aligned}`

The smaller run takes the same path and runs out sooner. On a call, the
callee with $`j` fewer steps runs out of fuel too, or returns what it
returned, leaving $`j` fewer steps, as the section on
{ref "The-fir-specification--Execution--The-runs-of-a-function___-and-fuel-monotonicity"}[the runs of a function]
proves; the caller then goes on with $`j` fewer steps. The section on
{ref "The-fir-specification--Execution--Replacing-a-callee"}[replacing a callee]
uses this to find, for each argument vector, a budget from which a run
never runs out of fuel, unless it runs out at every budget.
:::
