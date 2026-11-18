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

:::moduleDocs (fingerprint := "1403958685840523458")
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

:::readable Fir.Aggregate.number_ofNat Fir.Aggregate.le_of_number Fir.Aggregate.decodeNumber_app Fir.Aggregate.le_of_decodeNumber (fingerprint := "12354520816417280803")
*Theorems: the numbers of a layout.* A natural number within the limit,
$`2^{64} - 1`, is the number that its integer writes, and $`h(N)` writes
$`N` for every word $`h`; a number that an integer, or an attribute,
writes is within the limit.
:::

:::readable Fir.Attr.IsType.typeShaped Fir.Attr.isType_of_typeShaped (fingerprint := "10047053259525832746")
*Theorems: types and the form of a type.* A type has the form of a type,
and an attribute in the form of a type that can be written is a type.
:::

:::readable Fir.Field.decode_attr Fir.Field.wellFormed_of_decode (fingerprint := "11543767479898167766")
*Theorems: a field has one spelling.* A field whose offset and count are
within the limit, and whose type is written as a type and decodes back,
decodes back from what it writes. A field that decodes from an attribute
that can be written has its numbers within the limit, and its type is
written as a type and decodes back, when the dialect's types decode only
from what they write, as a lawful text's do.
:::
