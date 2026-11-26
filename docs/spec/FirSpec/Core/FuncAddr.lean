import VersoManual
import Fir.Core.FuncAddr
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on function address rules, which renders
`Fir.Core.FuncAddr` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Function address rules: readable blocks" =>

:::moduleDocs (fingerprint := "17485648691193492596")
:::

:::readable Fir.Core.funcAddrValue (fingerprint := "1779684139839533652")
*Definition: the rule of $`\mathsf{funcaddr}`.* Where the
{ref "The-fir-specification--Memory--The-items-a-run-gives-each-op"}[items]
of a run place the function $`f` as the allocation $`a` of memory 0, the
address of $`f` in the memory $`N` is the pointer of provenance $`a` at
offset 0 when $`N = 0`:

$$`\mathsf{funcaddr}^{0}_{a} = (a, 0)`

When the run places no function $`f`, or $`N` is not 0, it is the pointer
with no provenance at offset 0, $`(\bot, 0)`, through which every access is
UB. A run of a valid module places $`f`, and validation asks $`N = 0`.
Either way the rule is never UB and gives no poison. The allocation has no
units, so every access through the pointer is out of bounds.
:::

:::readable Fir.Core.funcAddrResult (fingerprint := "1294291223734899111")
*Definition: the result of $`\mathsf{funcaddr}`.* The one result of
$`\mathsf{funcaddr}~f~N`, where the run places its function at $`a`, is
the pointer $`\mathsf{funcaddr}^{N}_a`, never poison.
:::
