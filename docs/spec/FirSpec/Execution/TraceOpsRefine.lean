import VersoManual
import Fir.Execution.TraceOpsRefine
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a traced run of ops on refined environments and states, which renders
`Fir.Execution.TraceOpsRefine` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "A traced run of ops on refined environments and states: readable blocks" =>

:::moduleDocs (fingerprint := "3910815211414401764")
:::

:::readable Fir.Result.InStep Fir.TraceEnd.Allows.exitFrame Fir.TraceEnd.Allows.ub_prefix (fingerprint := "17434285451285169466")
*Definition: in step.* What a source's run of ops ends with allows, in
step, what the target's ends with when both return, the second values
refining the first's, with the same steps left, or both run out of fuel.

*Theorems.* Leaving a frame keeps one way of ending allowing another. UB after acts
$`t` that are a refined prefix of $`t'` allows every way that the target
ends after $`t'`.
:::

:::readable Fir.Func.traceCall_allowed Fir.Func.traceOps_allowed (fingerprint := "13802294596748228481")
*Theorem: traced runs of ops in step.* When every terminator and every op
with no callee of the module's functions, of the function $`f` and of
$`os` is monotone in the traced layer, and so is the external-call rule at
each of their other ops, then from environments
$`\varepsilon \sqsubseteq \varepsilon'` and traced states
$`s \sqsubseteq s'`, at every budget $`n`, each path of the run of $`os`
from $`\varepsilon'` and $`s'` that is not stuck is allowed in step by a
path of the run of $`os` from $`\varepsilon` and $`s`, at the same budget
$`n`: a return of values that the target's refine with the same steps
left, or running out of fuel, each after acts that the target's refine one
by one, in a traced state that the target's refines; or UB after a
refined prefix of the target's acts. Calls and recursion are included: a
call enters the same callee in both, in a frame, and its return, in step,
leaves the same steps in both; a call to a declaration runs the same
external-call rule in both, which is monotone.
:::
