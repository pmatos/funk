import VersoManual
import Fir.Core.LoadTextLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on loads reading back, which renders
`Fir.Core.LoadTextLaws` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Loads read back: readable blocks" =>

:::moduleDocs (fingerprint := "7440328115179457993")
:::

:::readable Fir.Core.word_of_decodeOrdering Fir.Core.decodeLoad_loadAttrs Fir.Core.decodeLoad_eq (pin := Fir.Core.decodeLoad) (pin := Fir.Core.loadAttrs) (fingerprint := "16521930911237614478")
*Theorems: every $`\mathsf{load}` reads back from its spelling, and only
from it.* The word that names an ordering is that ordering's word. For
every ordering $`o`, width $`W`, alignment $`a` and memory $`N`, valid or
not:

$$`\mathrm{decodeload}(\mathrm{loadattrs}(o, a), \mathsf{ptr}\langle N \rangle, \mathsf{i}W) = \mathsf{load}_N~o~W~a`

And if $`\mathrm{decodeload}(a^*, t^*, r^*) = op`, then $`op` is named
`load`, its attributes are $`a^*`, it has the operand types $`t^*` and the
result types $`r^*`. These are the cases of $`\mathsf{load}` in the
{ref "The-fir-specification--Text-format--The-core-dialect___s-text-is-lawful"}[laws of the core dialect's text].
:::

:::readable Fir.Core.loadAttrs_writable (pin := Fir.Attr.Writable) (fingerprint := "4202044539923570216")
*Theorem: the attributes of $`\mathsf{load}` are written as tokens.* The
word of an ordering is a word, and $`\mathtt{align}(a)` a word applied to
an integer, which the
{ref "The-fir-specification--Text-format--Tokens"}[lexer] reads as one
attribute each.
:::
