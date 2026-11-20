import VersoManual
import Fir.Core.MemSetText
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on fills in text, which
renders `Fir.Core.MemSetText` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Fills in text: readable blocks" =>

:::moduleDocs (fingerprint := "17480349319958099658")
:::

:::readable Fir.Core.decodeMemSet (pin := Fir.Core.decodeOrdering) (fingerprint := "11984578854323030551")
*Definition: how a fill is read.* A fill is named `memset`. It reads from
one attribute, the word of its ordering $`o`, and from the operand types
$`[\mathsf{ptr}\langle N \rangle, \mathsf{i}V, \mathsf{i}W]` with no
result:

$$`\mathrm{decodememset}([o], [\mathsf{ptr}\langle N \rangle, \mathsf{i}V, \mathsf{i}W], []) = \mathsf{memSet}_N~o~V~W`

Every other shape, an `align(A)` attribute, a missing ordering, a value
that is not an integer, or a result included, does not decode. Every
ordering and every width $`V` decodes; the
{ref "The-fir-specification--Validation--Core-rules"}[core rules]
accept only $`\mathsf{nonatomic}`, and the data layout only a $`V` as wide
as a unit of memory $`N`. For example, `memset nonatomic %d, %v, %n`
writes `%n` copies of the unit `%v` through `%d`.
:::
