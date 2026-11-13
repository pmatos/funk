import VersoManual
import Fir.Text.LayoutLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the data layout's text, proved, which
renders `Fir.Text.LayoutLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The data layout's text, proved: readable blocks" =>

:::moduleDocs (fingerprint := "12093234912984776982")
:::

:::readable Fir.MemLayout.number_ofNat Fir.MemLayout.le_of_number (fingerprint := "3126547449366373692")
*Theorem: the numbers of an entry.* An integer that writes a natural number
$`n` no larger than the limit reads back as $`n`, and an integer that reads
as a number reads as one no larger than the limit.
:::

:::readable Fir.ByteOrder.decode_word (fingerprint := "5128286983046042959")
*Theorem: a byte order reads back.* The word that writes a byte order reads
back as that byte order.
:::

:::readable Fir.MemLayout.decode_attr (fingerprint := "15072203736912766205")
*Theorem: an entry reads back.* For every entry $`e` whose numbers are
within the limit, decoding what $`e` writes gives $`e` back:

$$`\mathrm{decode}(\mathrm{attr}(e)) = e`
:::

:::readable Fir.MemLayout.decodeTail_le Fir.MemLayout.inLimits_of_decode (fingerprint := "8771757037091226587")
*Theorem: what decodes is within the limit.* An attribute decodes only to
an entry whose numbers, the alignment that it gives included, are within
the limit. So every module that a parser gives has a layout that it can
print and read back.
:::

:::readable Fir.MemLayout.attr_isType (fingerprint := "1540924113981596719")
*Theorem: an entry is written as a type.* What an entry writes is a type of
the grammar: the word `memory` applied to attributes that can be written.
So the reader of types reads it back, and its tokens can be written.
:::
