import VersoManual
import Fir.Core.StoreTextLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on stores reading back, which renders
`Fir.Core.StoreTextLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Stores read back: readable blocks" =>

:::moduleDocs (fingerprint := "14509812814199035746")
:::

:::readable Fir.Core.decodeStore_loadAttrs Fir.Core.decodeStore_storePtr Fir.Core.decodeStore_eq (pin := Fir.Core.decodeStore) (pin := Fir.Core.loadAttrs) (fingerprint := "6792575262468041391")
*Theorems: every $`\mathsf{store}` reads back from its spelling, and only
from it.* For every ordering $`o`, width $`W`, alignment $`a` and memories
$`N` and $`M`, valid or not:

$$`\mathrm{decodestore}(\mathrm{loadattrs}(o, a), [\mathsf{i}W, \mathsf{ptr}\langle N \rangle], []) = \mathsf{store}_N~o~W~a`

$$`\mathrm{decodestore}(\mathrm{loadattrs}(o, a), [\mathsf{ptr}\langle M \rangle, \mathsf{ptr}\langle N \rangle], []) = \mathsf{store}_N~o~\mathsf{ptr}\langle M \rangle~a`

And if $`\mathrm{decodestore}(a^*, t^*, r^*) = op`, then $`op` is named
`store`, its attributes are $`a^*`, it has the operand types $`t^*` and the
result types $`r^*`. Its attributes are those of a load, which are
{ref "The-fir-specification--Text-format--Loads-read-back"}[written as tokens].
These are the cases of $`\mathsf{store}` in the
{ref "The-fir-specification--Text-format--The-core-dialect___s-text-is-lawful"}[laws of the core dialect's text].
:::
