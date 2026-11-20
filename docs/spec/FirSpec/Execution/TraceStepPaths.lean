import VersoManual
import Fir.Execution.TraceStepPaths
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a traced run of ops, one step at a time, which renders
`Fir.Execution.TraceStepPaths` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "A traced run of ops, one step at a time: readable blocks" =>

:::moduleDocs (fingerprint := "8136399610174180121")
:::

:::readable Fir.TraceM.run_inFrame Fir.Func.traceOps Fir.Func.traceCall (fingerprint := "11262141160603910468")
*Definition: traced runs of ops.* The traced run of the ops $`os` of $`f`
in the environment $`\varepsilon`, with $`n` steps of fuel, from the traced
state $`s`, is the interpreter's run in the traced layer, read from
$`s`. A callee runs in a frame: from $`s` with a new frame entered, and
each path that does not hit UB leaves the frame.
:::

:::readable Fir.Func.TStepPath Fir.Func.tStepPath_iff (fingerprint := "3424079462557353236")
*Definition and theorem: the ways a step goes on.* A path of the traced run
of $`o :: os` with $`n + 1` steps, from $`s`, that is not stuck goes on in
one of eight ways, each from $`s`:

* a terminator's exit hits UB after the acts $`t`; or returns, after $`t`,
  in $`s'`, giving its operands back with $`n` steps left; or goes to a
  block, after $`t`, from $`s'`, whose run with $`n` steps ends the path
  after $`t`;
* an op with no callee hits UB after $`t`, or gives results after $`t`,
  in $`s'`, from which the rest of the block runs with $`n` steps, after
  $`t`;
* a call's callee, in its frame, hits UB, or runs out of fuel, or returns
  values after $`t` in $`s'` with $`k` steps left, and the rest of the
  block runs from $`s'` with $`\min(k, n)` steps, after $`t`.
:::

:::readable Fir.Func.traceOps_zero Fir.Func.traceOps_nil (fingerprint := "1211920152472717101")
*Theorems.* A traced run with no fuel runs out of fuel, showing nothing,
and only so. A block with no op left is stuck.
:::
