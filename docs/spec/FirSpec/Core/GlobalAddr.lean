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

:::moduleDocs (fingerprint := "6360350781557945721")
:::

:::readable Fir.Core.globalAddrValue (fingerprint := "15220210227533566528")
*Definition: the rule of $`\mathsf{globaladdr}`.* Where the
{ref "The-fir-specification--Memory--The-items-a-run-gives-each-op"}[items]
of a run place the global $`s` in the memory $`m`, as its allocation
$`a`, the address of $`s` in the memory $`N` is the pointer of provenance
$`a` at offset 0 when $`m = N`:

$$`\mathsf{globaladdr}^{N}_{(N, a)} = (a, 0)`

When the run places no global $`s`, or places it in a memory other than
$`N`, it is the pointer with no provenance at offset 0, $`(\bot, 0)`,
through which every access is UB, so a pointer of
$`\mathsf{ptr}\langle N \rangle` never names an allocation of another
memory. A run of a valid module places $`s` in $`N`, as validation asks.
Either way the rule is never UB and gives no poison.
:::

:::readable Fir.Core.globalAddrResult (fingerprint := "7072969785548911122")
*Definition: the result of $`\mathsf{globaladdr}`.* The one result of
$`\mathsf{globaladdr}~s~N`, where the run places its global at $`g`, is
the pointer $`\mathsf{globaladdr}^{N}_g`, never poison.
:::
