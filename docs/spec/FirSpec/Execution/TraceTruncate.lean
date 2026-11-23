import VersoManual
import Fir.Execution.TraceTruncate
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on truncating a traced run, which renders
`Fir.Execution.TraceTruncate` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Truncating a traced run: readable blocks" =>

:::moduleDocs (fingerprint := "2639438574725953649")
:::

:::readable Fir.Func.traceOps_cut (fingerprint := "2639438574725953649")
*Theorem: truncation.* When every path of every op,
of every external call and of every rule that picks a callee shows exactly
one step, and $`W > 0` exceeds the length of every chain of calls of the
module by at least two, each path of a traced run of ops with $`n + j` steps of fuel
that is not stuck has a cut among the paths of the run with $`n`, from the
same environment and traced state.
:::
