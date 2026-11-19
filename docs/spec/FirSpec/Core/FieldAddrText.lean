import VersoManual
import Fir.Core.FieldAddrText
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on field addresses in text, which
renders `Fir.Core.FieldAddrText` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Field addresses in text: readable blocks" =>

:::moduleDocs (fingerprint := "7924608909497886101")
:::

:::readable Fir.Core.fieldAddrAttrs Fir.Core.decodeFieldAddr (fingerprint := "11526414541414562509")
*Definitions: how $`\mathsf{fieldaddr}` is written and read.* The
attributes of $`\mathsf{fieldaddr}~s~j` are the symbol $`@s` and the
integer $`j`. They read back as that op from a pointer operand, or a
pointer and an integer of any width, and a pointer result of the same
memory, when $`j` is not negative. Every other list of attributes, and
every other shape of operands and results, does not decode.
:::

:::readable Fir.Core.decodeFieldAddr_attrs Fir.Core.decodeFieldAddr_eq (fingerprint := "2813599668669215439")
*Theorems: $`\mathsf{fieldaddr}` reads back.* Each
$`\mathsf{fieldaddr}~s~j~N~w` reads back from its attributes, its operand
types and its result type, and an op that decodes from attributes and
types is a $`\mathsf{fieldaddr}` whose own attributes and types they are.
:::
