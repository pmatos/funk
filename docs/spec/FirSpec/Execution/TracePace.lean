import VersoManual
import Fir.Execution.TracePace
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the fuel of a return, which renders
`Fir.Execution.TracePace` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The fuel of a return: readable blocks" =>

:::moduleDocs (fingerprint := "13644898566718814199")
:::

:::readable Fir.TraceEnd.RetPaced Fir.TraceEnd.RetPaced.after_step (fingerprint := "6800816011288160283")
*Definition: a paced return.* A return of a run of $`os` with $`n` steps of
fuel, that leaves $`k` after a marked trace of $`m` steps, is paced by
$`W` when $`k + m \le n`, $`0 < m`, and $`n + W \le k + W m + c + 1`,
where $`os` starts a chain of $`c` calls.

*Theorem.* After an op of one step, from ops that start no call, a paced
return stays paced, one step of fuel later.
:::

:::readable Fir.Func.traceOps_retPaced (fingerprint := "17858191772949970459")
*Theorem.* When every path of every op shows exactly one step, and $`W`
exceeds the length of every chain of calls of the module by at least one,
every return of a traced run of ops is paced by $`W`.
:::
