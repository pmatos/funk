import VersoManual
import Fir.Execution.TraceStepWays
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the ways a traced step goes on, which renders
`Fir.Execution.TraceStepWays` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The ways a traced step goes on: readable blocks" =>

:::moduleDocs (fingerprint := "4088167876067259266")
:::

:::readable Fir.TraceM.run_inFrame Fir.Func.traceOps Fir.Func.traceCall (fingerprint := "89150425833785351")
*Definition: traced runs of ops.* The traced run of the ops $`os` of $`f`
in the environment $`\varepsilon`, with $`n` steps of fuel, from the traced
state $`s`, is the interpreter's run in the traced layer, read from
$`s`. A callee runs in a frame: from $`s` with a new frame entered, and
each path that does not hit UB leaves the frame.
:::

:::readable Fir.Func.TCallsAt Fir.Func.TCallsAt.le Fir.Func.TCallsAt.up Fir.Func.TCallsAt.down Fir.Func.TCallsAt.at Fir.Func.TCallsAt.picked_of_lt (pin := Fir.Module.callable) (fingerprint := "12213682169976675537")
*Definition: the call of an op, in the traced layer.* The op $`o`, on the
operands $`\vec{v}`, from the traced state $`s`, with $`n` steps left
after its own, calls the symbol $`g` on the arguments $`\vec{a}` with $`n'`
steps left for the call, from the traced state $`s_1`, after the acts
$`t_0`: the symbol that $`o` names, on $`\vec{v}`, with $`n' = n`, from
$`s_1 = s`, after no act; or, when the callee of $`o` is picked, a symbol
that its rule picks from $`s`, ending in $`s_1` after the acts $`t_0`, on
$`\vec{v}` but its first value, with $`n = n' + 1` (#235).

*Theorems.* As for the
{ref "The-fir-specification--Execution--The-callee-of-a-call"}[call of an op]
in the set monad: $`n' \le n \le n' + 1`; with $`j` more steps after the
op, the call leaves $`j` more; with $`j` fewer, $`j` fewer, unless the
callee is picked and no step is left for the call; the call is the same at
every budget that leaves it $`m` steps; and a call that leaves fewer steps
than its op picks its callee.
:::

:::readable Fir.Func.TStepPath (fingerprint := "3355755156873989395")
*Definition: the ways a step goes on.* A path of the traced run of
$`o :: os` with $`n + 1` steps, from $`s`, that is not stuck goes on in
one of twelve ways, each from $`s`:

* a terminator's exit hits UB after the acts $`t`; or returns, after $`t`,
  in $`s'`, giving its operands back with $`n` steps left; or goes to a
  block, after $`t`, from $`s'`, whose run with $`n` steps ends the path
  after $`t`;
* an op with no callee hits UB after $`t`, or gives results after $`t`,
  in $`s'`, from which the rest of the block runs with $`n` steps, after
  $`t`;
* an op calls a symbol on arguments with $`n'` steps, from $`s_1`, after
  the acts $`t_0`, as above; and the symbol names a function, whose run in
  its frame, from $`s_1`, hits UB, or runs out of fuel, or returns values
  after $`t` in $`s'` with $`k` steps left, and the rest of the block runs
  from $`s'` with $`\min(k, n')` steps, after $`t_0` then $`t`; or the
  symbol names no function of the module, which declares it for the
  call's types, and the external-call rule hits UB after $`t`, or gives
  results of the call's result types after $`t`, in $`s'`, from which the
  rest of the block runs with $`n'` steps, all after $`t_0`;
* an op whose callee is picked: its rule hits UB after $`t`, or picks a
  symbol after $`t` in $`s_1` with no step left, $`n = 0`, and the path
  runs out of fuel after $`t`, in $`s_1`.
:::

:::readable Fir.Func.traceOps_zero Fir.Func.traceOps_nil (fingerprint := "18066484428726939998")
*Theorems.* A traced run with no fuel runs out of fuel, showing nothing,
and only so. A block with no op left is stuck.
:::
