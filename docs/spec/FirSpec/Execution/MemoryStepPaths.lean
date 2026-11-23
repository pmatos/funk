import VersoManual
import Fir.Execution.MemoryStepPaths
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the ways a step with memory goes on,
which renders `Fir.Execution.MemoryStepPaths` (ADR-2026-11-05-2012). Each
block explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "The ways a step with memory goes on: readable blocks" =>

:::moduleDocs (fingerprint := "4786903917007213429")
:::

:::readable Fir.Func.MemCallsAt Fir.Func.MemStepPath Fir.Func.memStepPath_iff (pin := Fir.Func.runOps) (pin := Fir.Ev.NotStuck) (fingerprint := "6468017461194797408")
*Definition and theorem: the ways a step with memory goes on.* A path of
$`\mathrm{ops}_M(n + 1, f, E, o~o^*) \mathbin{@} S` that is not stuck is
exactly a path that the op $`o` goes on by, from $`S`. In each, $`o` owns
no region of the core's kind and its operands $`\vec{v}` are found in
$`E`. Then:

* $`o` is a terminator, the last op of its block, and
  $`\mathrm{exit}_o(\vec{v})(S)` hits UB, which the path hits; or returns
  with the memories $`S'`, and the path returns $`((\vec{v}, S'), n)` when
  $`o`'s operands are of $`f`'s result types; or goes to the successor
  $`i` with the memories $`S'`, and the path goes on by the jump's block,
  from $`S'`, with $`n` steps;
* $`o` calls no function, and $`\mathrm{denote}_o(\vec{v})(S)` hits UB,
  which the path hits, or gives results $`\vec{r}` with the memories
  $`S'`, which bind, and the path goes on from $`S'` with $`n` steps;
* $`o` calls a symbol on arguments $`\vec{a}` with $`n'` steps, from the
  memories $`S_1`: the symbol it names, on $`\vec{v}`, with $`n' = n`,
  from $`S_1 = S`; or, when its callee is picked, the symbol its rule
  $`\mathrm{pick}_o(\vec{v})(S)` picks, on $`\vec{v}` but its first
  value, with $`n = n' + 1`, from the memories $`S_1` the rule ends with
  (#235). Then the symbol names the function $`g` of $`M`, which the call
  enters on $`\vec{a}`, and
  $`\mathrm{call}_M(n', g, E_g, b^*) \mathbin{@} S_1` hits UB or runs out
  of fuel, which the path does; or returns $`((\vec{w}, T), k)`, of the
  call's result types, which bind, and the path goes on from $`T` with
  $`\min(k, n')` steps; or the symbol names no function of $`M`, $`M`
  declares it for the types of $`\vec{a}` and the results of $`o`, and the
  external-call rule, UB with memory, ends the path in UB;
* $`o`'s callee is picked and its rule hits UB, which the path hits, or
  picks a symbol with no step left, $`n = 0`, and the path runs out of
  fuel.

This mirrors
{ref "The-fir-specification--Execution--The-ways-a-step-goes-on"}[the ways a step goes on]
in the set monad, each step from the memories that the step before it
ended with.
:::
