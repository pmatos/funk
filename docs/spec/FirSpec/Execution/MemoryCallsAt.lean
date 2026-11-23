import VersoManual
import Fir.Execution.MemoryCallsAt
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the callee of a call, with memory, which renders
`Fir.Execution.MemoryCallsAt` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The callee of a call, with memory: readable blocks" =>

:::moduleDocs (fingerprint := "6741283884465763646")
:::

:::readable Fir.Func.MemCallsAt.le Fir.Func.MemCallsAt.up Fir.Func.MemCallsAt.down Fir.Func.MemCallsAt.at Fir.Func.MemCallsAt.picked_of_lt (pin := Fir.Func.MemCallsAt) (fingerprint := "2859109850014263065")
*Theorems: the steps of a call, with memory.* As for the
{ref "The-fir-specification--Execution--The-callee-of-a-call"}[call of an op]
in the set monad, a call with memory leaves its callee $`n'` steps with
$`n' \le n \le n' + 1`; with $`j` more steps after the op, it leaves $`j`
more, from the same memories; with $`j` fewer, $`j` fewer, unless the
callee is picked and no step is left for the call; it is the same call at
every budget that leaves it $`m` steps; and a call that leaves fewer steps
than its op picks its callee.
:::
