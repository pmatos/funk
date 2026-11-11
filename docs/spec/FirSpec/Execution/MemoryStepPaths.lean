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

:::moduleDocs (fingerprint := "11001519427309581654")
:::

:::readable Fir.runFrom_liftExcept_bind Fir.runFrom_lift_bind Fir.runFrom_bindRun (pin := Fir.runFrom) (pin := Fir.Ev.NotStuck) (fingerprint := "10455669558575755810")
*Theorems: paths of a sequence, from given memories.* Read
{ref "The-fir-specification--Memory--How-a-run-with-memory-ends"}[from the memories S],
a path of a run of ops that starts with a check of the interpreter, and is
not stuck, goes on from the value that the check holds, from $`S`. One that
starts with a computation $`c` of the state layer goes on from a result
$`a` of $`c(S)` with the memories $`T` it ends with, or ends in UB where
$`c(S)` does. One that starts with a run of ops $`x`, and goes on by $`K`,
which runs out of fuel when $`x` does, goes on by $`K` from a return of
$`x` with the memories $`T` it ends with, or ends where $`x` runs out of
fuel or hits UB.
:::

:::readable Fir.runFrom_ret_iff Fir.runFrom_exh_iff Fir.runFrom_ub_iff (pin := Fir.Result.withState) (fingerprint := "14741995060649176328")
*Theorems: how a run of ops ends, with or without its memories.* A run of
ops from $`S`, read with the memories its returns end with, returns
$`((a, T), k)` exactly when, read from $`S`, it ends with the return
$`(a, k)` and the memories $`T`; it runs out of fuel exactly when it ends
so with some memories; and it hits UB exactly when it does.
:::

:::readable Fir.Func.memOps Fir.Func.memCall (fingerprint := "4857219975976549756")
*Definitions: a run of ops with memory, and a callee's run in its frame.*
$`\mathrm{ops}_M(n, f, E, o^*) \mathbin{@} S` is the interpreter's run of
the ops $`o^*` of $`f` in the state layer, with $`n` steps, in the
environment $`E`, read from the memories $`S`: each return carries the
values, the memories it ends with, and the steps it leaves.
$`\mathrm{call}_M(n, g, E, o^*) \mathbin{@} S` is the same run in a call's
frame: from $`\mathrm{enter}(S)`, and each return leaves the frame.
:::

:::readable Fir.Func.MemStepPath Fir.Func.memStepPath_iff (pin := Fir.Func.runOps) (pin := Fir.Ev.NotStuck) (fingerprint := "10893883184050481262")
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
* $`o` calls the function $`g` of $`M`, which it enters on $`\vec{v}`, and
  $`\mathrm{call}_M(n, g, E_g, b^*) \mathbin{@} S` hits UB or runs out of
  fuel, which the path does; or returns $`((\vec{w}, T), k)`, of the
  call's result types, which bind, and the path goes on from $`T` with
  $`\min(k, n)` steps.

This mirrors
{ref "The-fir-specification--Execution--The-ways-a-step-goes-on"}[the ways a step goes on]
in the set monad, each step from the memories that the step before it
ended with.
:::

:::readable Fir.Func.run_memOps_zero Fir.Func.run_memOps_nil (pin := Fir.Func.runOps) (pin := Fir.Ev.NotStuck) (fingerprint := "7693370220352180185")
*Theorems: no fuel, and no op left.* From any memories, a run with no
fuel runs out of fuel, and only so; a block with no op left is stuck.
:::
