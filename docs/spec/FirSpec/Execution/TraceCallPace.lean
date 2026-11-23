import VersoManual
import Fir.Execution.TraceCallPace
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a callee's return, paced, which renders
`Fir.Execution.TraceCallPace` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "A callee's return, paced: readable blocks" =>

:::moduleDocs (fingerprint := "6409271475325835690")
:::

:::readable Fir.Func.traceCall_retPaced Fir.Func.traceCall_retPaced_le Fir.Func.traceCall_cut_ret (fingerprint := "5222943014813931354")
*Theorems: a callee's return.* When every path of every op and
of every external call shows exactly one
step, a return of a callee's ops in its frame with $`k` steps left after the
marked trace $`t` at the budget $`U` shows a step, and leaves
$`U - k \ge \mathrm{ticks}(t)`. When $`W` exceeds the length of every chain of
calls of the module by at least two, $`U - k \le W \cdot \mathrm{ticks}(t)`.

Cut to a budget $`n < U`, the return comes back with $`k - (U - n)` steps left
when $`k \ge U - n`. Otherwise the callee runs out of fuel at $`n`, after a
marked trace that starts $`t`, of at most $`n` steps, which is all of $`t` or
has $`n \le W m + c` for its $`m` steps and a chain of $`c` calls.
:::
