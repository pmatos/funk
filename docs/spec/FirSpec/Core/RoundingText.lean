import VersoManual
import Fir.Core.RoundingText
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the rounding mode in text, which
renders `Fir.Core.RoundingText` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The rounding mode in text: readable blocks" =>

:::moduleDocs (fingerprint := "11489202054206564164")
:::

:::readable Fir.Core.RoundingMode.word Fir.Core.decodeRoundingMode Fir.Core.roundAttr Fir.Core.decodeRound (fingerprint := "6973648837649998569")
*Definition: the rounding mode in text.* Each mode is written as its
name: $`\mathtt{rne}`, $`\mathtt{rna}`, $`\mathtt{rtp}`, $`\mathtt{rtn}`
and $`\mathtt{rtz}`, and a word names a mode only when it is one of
these five. An op that rounds with the mode $`r` carries one attribute,
$`\mathtt{round}(r)`, the word $`\mathtt{round}` applied to the mode's
word. Attributes read as a mode only when they are exactly one such
attribute: no attribute, $`\mathtt{round(RNE)}`, $`\mathtt{round()}`,
$`\mathtt{round(rne, rne)}`, the bare word $`\mathtt{rne}` and two
attributes do not.
:::

:::readable Fir.Core.decodeRoundingMode_word Fir.Core.word_of_decodeRoundingMode Fir.Core.decodeRound_roundAttr Fir.Core.eq_of_decodeRound Fir.Core.roundAttr_writable (fingerprint := "14261132520676345602")
*Theorems: the mode reads back.* Each mode reads back from its word, and
its word is the only one that names it. So each mode reads back from its
attribute, attributes that read as a mode are exactly that mode's
attribute, and the attribute is written as tokens.
:::
