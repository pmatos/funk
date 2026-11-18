import VersoManual
import Fir.Core.MemCopyTextLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on copies and moves reading back, which
renders `Fir.Core.MemCopyTextLaws` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Copies and moves read back: readable blocks" =>

:::moduleDocs (fingerprint := "10545675350943994887")
:::

:::readable Fir.Core.decodeMemCopy_loadAttrs Fir.Core.decodeMemCopy_eq Fir.Core.CopyKind.name_isWord (pin := Fir.Core.decodeMemCopy) (pin := Fir.Core.loadAttrs) (pin := Fir.Core.CopyKind.name) (fingerprint := "11556063497069557712")
*Theorems: every copy and move reads back from its spelling, and only from
it.* For every kind $`k`, ordering $`o`, width $`W` and memory $`N`,
valid or not:

$$`\mathrm{decodememcopy}_k(\mathrm{loadattrs}(o, \mathrm{none}), [\mathsf{ptr}\langle N \rangle, \mathsf{ptr}\langle N \rangle, \mathsf{i}W], []) = \mathsf{memCopy}_N~k~o~W`

And if $`\mathrm{decodememcopy}_k(a^*, t^*, r^*) = op`, then $`op` is
named as $`k` is, `memcpy` or `memmove`, its attributes are $`a^*`, it has
the operand types $`t^*` and the result types $`r^*`. Both names are
words. These are the cases of $`\mathsf{memcpy}` and $`\mathsf{memmove}`
in the
{ref "The-fir-specification--Text-format--The-core-dialect___s-text-is-lawful"}[laws of the core dialect's text].
:::
