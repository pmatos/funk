import VersoManual
import Fir.Core.MemSetTextLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on fills read back, which
renders `Fir.Core.MemSetTextLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Fills read back: readable blocks" =>

:::moduleDocs (fingerprint := "14954070489155432549")
:::

:::readable Fir.Core.decodeMemSet_loadAttrs Fir.Core.decodeMemSet_eq (pin := Fir.Core.decodeMemSet) (pin := Fir.Core.loadAttrs) (fingerprint := "6652108335918399781")
*Theorems: every fill reads back from its spelling, and only from it.*
For every ordering $`o`, widths $`V` and $`W` and memory $`N`, valid or
not:

$$`\mathrm{decodememset}(\mathrm{loadattrs}(o, \mathrm{none}), [\mathsf{ptr}\langle N \rangle, \mathsf{i}V, \mathsf{i}W], []) = \mathsf{memSet}_N~o~V~W`

And if $`\mathrm{decodememset}(a^*, t^*, r^*) = op`, then $`op` is named
`memset`, its attributes are $`a^*`, it has the operand types $`t^*` and
the result types $`r^*`. This is the case of $`\mathsf{memset}` in the
{ref "The-fir-specification--Text-format--The-core-dialect___s-text-is-lawful"}[laws of the core dialect's text].
:::
