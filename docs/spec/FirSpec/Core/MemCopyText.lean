import VersoManual
import Fir.Core.MemCopyText
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on copies and moves in text, which
renders `Fir.Core.MemCopyText` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Copies and moves in text: readable blocks" =>

:::moduleDocs (fingerprint := "2557598902953324294")
:::

:::readable Fir.Core.CopyKind.name Fir.Core.decodeMemCopy (pin := Fir.Core.decodeOrdering) (fingerprint := "1438967698719833527")
*Definitions: how a copy and a move are read.* A copy is named `memcpy`
and a move `memmove`. Each reads from one attribute, the word of its
ordering $`o`, and from the operand types
$`[\mathsf{ptr}\langle N \rangle, \mathsf{ptr}\langle N' \rangle, \mathsf{i}W]`
with no result:

$$`\mathrm{decodememcopy}_k([o], [\mathsf{ptr}\langle N \rangle, \mathsf{ptr}\langle N' \rangle, \mathsf{i}W], []) = \begin{cases} \mathsf{memCopy}_N~k~o~W & \text{if } N = N' \\ \text{none} & \text{otherwise} \end{cases}`

Every other shape, an `align(A)` attribute, a missing ordering, or a
result included, does not decode. Every ordering decodes; the
{ref "The-fir-specification--Validation--Core-rules"}[core rules]
accept only $`\mathsf{nonatomic}`. For example,
`memcpy nonatomic %d, %s, %n` copies `%n` units from `%s` to `%d`.
:::
