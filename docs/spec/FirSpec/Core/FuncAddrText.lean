import VersoManual
import Fir.Core.FuncAddrText
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on addresses of functions in text, which
renders `Fir.Core.FuncAddrText` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Addresses of functions in text: readable blocks" =>

:::moduleDocs (fingerprint := "10802287429967066327")
:::

:::readable Fir.Core.funcAddrAttrs Fir.Core.decodeFuncAddr (fingerprint := "10522557071896959188")
*Definitions: how $`\mathsf{funcaddr}` is written and read.* The one
attribute of $`\mathsf{funcaddr}~f` is the symbol $`@f`. It reads back as
that op from no operands and one pointer result, of any memory $`N`. Every
other list of attributes, and every other shape of operands and results,
does not decode.
:::

:::readable Fir.Core.decodeFuncAddr_attrs Fir.Core.decodeFuncAddr_eq (fingerprint := "13662879524839146676")
*Theorems: $`\mathsf{funcaddr}` reads back.* Each
$`\mathsf{funcaddr}~f~N` reads back from its attribute, its empty operand
types and its result type, and an op that decodes from attributes and
types is a $`\mathsf{funcaddr}` whose own attribute and types they are.
:::
