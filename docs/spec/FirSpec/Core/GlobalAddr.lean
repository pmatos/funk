import VersoManual
import Fir.Core.GlobalAddr
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on global address rules, which renders
`Fir.Core.GlobalAddr` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Global address rules: readable blocks" =>

:::moduleDocs (fingerprint := "7383995525567511730")
:::

:::readable Fir.Core.globalAddrValue (fingerprint := "16751499241651980524")
*Definition: the rule of $`\mathsf{globaladdr}`.* Where the
{ref "The-fir-specification--Memory--The-items-a-run-gives-each-op"}[items]
of a run place the global $`s` in the memory $`m`, as its allocation
$`a`, the address of $`s` is the pointer of provenance $`a` at offset 0:

$$`\mathsf{globaladdr}_{(m, a)} = (a, 0)`

When the run places no global $`s`, it is the pointer with no provenance
at offset 0, $`(\bot, 0)`, through which every access is UB. Either way
the rule is never UB and gives no poison.
:::

:::readable Fir.Core.globalAddrResult (fingerprint := "12310758031254197073")
*Definition: the result of $`\mathsf{globaladdr}`.* The one result of
$`\mathsf{globaladdr}~s~N`, where the run places its global at $`g`, is
the pointer $`\mathsf{globaladdr}_g`, never poison.
:::
