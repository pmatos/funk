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

:::moduleDocs (fingerprint := "7618379882577441334")
:::

:::readable Fir.Func.StepPath Fir.Func.stepPath_iff (pin := Fir.Func.runOps) (pin := Fir.Ev.NotStuck) (fingerprint := "9492912948227496896")
*Definition and theorem: the eleven ways a step goes on.* Write
$`\mathrm{run}_M(n, f, E, o^*)` for the
{ref "The-fir-specification--Execution--The-interpreter"}[run of the ops]
$`o^*` of the function $`f` of the module $`M`, in the environment $`E`,
with $`n` steps of fuel, and $`e \in \mathrm{run}_M(n, f, E, o^*)` when
one of its paths ends with $`e`. A run of ops that returns gives typed
values $`u^*` and the steps $`k` it leaves: $`\mathsf{ret}~(u^*, k)`.

Take a run $`\mathrm{run}_M(n + 1, f, E, o\,o'^*)` whose first op is $`o`.
In each of the eleven ways, $`o` owns no region of the core's kind, and
the values $`v^*` of
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

When $`o` is not a terminator, it calls a symbol $`s` on arguments
$`a^*`, with $`n'` steps for the call: $`s` is the symbol that $`o` names,
$`a^* = v^*` and $`n' = n`; or $`o`'s callee is picked, its rule
$`\mathrm{pick}_o(\mathrm{callable}_M(\ldots), v^*)` may end with $`s`,
$`a^*` is $`v^*` but its first value, and $`n = n' + 1`, one step for the
call (#235). When the module has the function
$`g = \mathrm{lookup}_M(s)`, entering it, $`\mathrm{enter}_g(a^*)`,
starts at the ops $`p^*` in the environment $`G`, and its run
$`\mathrm{run}_M(n', g, G, p^*)` may end:

6. with $`\mathsf{ub}~r`, and the path ends with $`\mathsf{ub}~r`;
7. with $`\mathsf{fuel\_exhausted}`, and the path ends so;
8. with $`\mathsf{ret}~(u^*, k)`, the types of $`u^*` are the result types
   of $`o`, the values $`u^*` are as many as the names $`x^*` of the
   results of $`o`, and the path ends with an end $`e` of
   $`\mathrm{run}_M(\min(k, n'), f, [x^* \mapsto u^*] \cdot E, o'^*)`.

When no function of the module has the symbol $`s`, and the module
{ref "The-fir-specification--Execution--The-external-call-rule"}[declares]
$`s` for the types of $`a^*` and the result types of $`o`:

9. the external-call rule, UB in the set monad, ends the path with
   $`\mathsf{ub}`, for the reason that an external call has no meaning
   without a world.

When $`o` is not a terminator and its callee is picked, its rule may also
end:

10. with $`\mathsf{ub}~r`, and the path ends with $`\mathsf{ub}~r`;
11. with a symbol, when $`n = 0`: no step is left for the call, and the
    path ends with $`\mathsf{fuel\_exhausted}`.

Here $`[x^* \mapsto w^*] \cdot E` binds each name to its value in front
of $`E`, and $`\mathrm{lookup}_M`, $`\mathrm{exit}_o`,
$`\mathrm{denote}_o` and $`\mathrm{enter}_g` are as in the
{ref "The-fir-specification--Execution--The-interpreter"}[interpreter],
which also says why a caller goes on with $`\min(k, n')` steps: a run
leaves at most the steps it was given, so this is $`k`.

*Theorem:* for every end $`e` that is not stuck,

$$`\begin{aligned} & e \in \mathrm{run}_M(n + 1, f, E, o\,o'^*) \\ \iff\ & \text{one of the eleven ways} \\ & \text{ends with } e \end{aligned}`

The refinement proofs of the next sections compare two runs path by path,
one step at a time. This says once every case of a step, so that they need
not unfold the interpreter.
:::

:::readable Fir.Func.run_runOps_zero Fir.Func.run_runOps_nil (pin := Fir.Func.runOps) (pin := Fir.Ev.NotStuck) (fingerprint := "8840420426461190377")
*Theorems: a run with no fuel, and a block with no op left.* For every
module $`M`, function $`f`, environment $`E`, ops $`o^*` and budget $`n`:

* $`e \in \mathrm{run}_M(0, f, E, o^*) \iff e = \mathsf{fuel\_exhausted}`:
  a run with no fuel runs out of fuel, and does nothing else;
* no end that is not stuck is an end of
  $`\mathrm{run}_M(n + 1, f, E, \epsilon)`: a block with no op left, and
  so no terminator, is stuck.

With the eleven ways above, these cover every run of ops.
:::
