import VersoManual
import Fir.Gpu.TextLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the laws of the text of `gpu`, which
renders `Fir.Gpu.TextLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The GPU dialect's text is lawful: readable blocks" =>

:::moduleDocs (fingerprint := "10250467856576467108")
:::

:::readable Fir.Gpu.Query.decode_name Fir.Gpu.Query.name_decode Fir.Gpu.Dim.decode_word Fir.Gpu.Dim.word_decode (fingerprint := "17115323010254968280")
*Theorem: the words of the questions and dimensions read back.* Reading
the name of a question gives the question, and a name reads only as the
question it names; the same holds of the word of each dimension.
:::

:::readable Fir.Gpu.Op.decode_encode Fir.Gpu.Op.encode_decode (fingerprint := "1317897471734365385")
*Theorem: an op of `gpu` reads back, and from its own text alone.* Every
op of `gpu` decodes from its name and attributes at its operand and result
types; and an op decodes only from its own name, attributes, operand types
and result types.
:::

:::readable Fir.Gpu.decodeTy_attr Fir.Gpu.attr_decodeTy Fir.Gpu.attr_isType (fingerprint := "12504058718153324292")
*Theorem: the types of `gpu` read back.* Each valid type of `gpu`, a core
type, reads back from what `gpu` writes, a type reads as what was written,
and each valid type is written as a type, as the core's laws give.
:::

:::readable Fir.Gpu.lawfulDialectText Fir.Gpu.instLawfulDialectText (fingerprint := "14356578165805406727")
*Theorem: the text of `gpu` is lawful.* The text of `gpu` over the core
meets the seven laws of a dialect's text: ops and types read back, read
only from their own text, op names are words, attributes can be written,
and valid types are written as types.
:::

:::readable Fir.Gpu.dialectsAll_attrs Fir.Gpu.lawfulDialectName (fingerprint := "16019133885697219364")
*Theorem: `gpu` writes its words under its name.* The words of an op's
attribute name the dialect $`\texttt{gpu}` alone. So each op name and each
dimension of `gpu` is a word of $`\texttt{gpu}`, and `gpu` has no type of
its own and registers no region kind or kind of item.
:::

:::readable Fir.Gpu.name_new Fir.Gpu.instLawfulDialectTextSum Fir.Gpu.validIsWellFormed Fir.Gpu.printThenParse Fir.Gpu.parseThenPrint Fir.Gpu.print_injective (fingerprint := "4004277751942047869")
*Theorem: the round trip holds for the sum of the core and `gpu`.* The
name $`\texttt{gpu}` is new to the core, whose set is empty, so the sum's
text is lawful with no new assumption. Then every valid module of the sum
is well formed; $`\mathrm{parse}(\mathrm{print}(m)) = m` for every
well-formed module $`m` of the sum, a host module with a device module
included; $`\mathrm{print}(\mathrm{parse}(t)) = t` for every text $`t`
printed from one; and two valid modules of the sum that print the same text
are the same module.
:::
