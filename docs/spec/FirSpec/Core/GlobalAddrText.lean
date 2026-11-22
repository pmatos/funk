import VersoManual
import Fir.Core.GlobalAddrText
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on addresses of globals in text, which
renders `Fir.Core.GlobalAddrText` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Addresses of globals in text: readable blocks" =>

:::moduleDocs (fingerprint := "13366237319441740475")
:::

:::readable Fir.Core.globalAddrAttrs Fir.Core.decodeGlobalAddr (fingerprint := "7872527083620493349")
*Definitions: how $`\mathsf{globaladdr}` is written and read.* The one
attribute of $`\mathsf{globaladdr}~s` is the symbol $`@s`. It reads back as
that op from no operands and one pointer result, of any memory $`N`. Every
other list of attributes, and every other shape of operands and results,
does not decode.
:::

:::readable Fir.Core.decodeGlobalAddr_attrs Fir.Core.decodeGlobalAddr_eq (fingerprint := "2557081631362364553")
*Theorems: $`\mathsf{globaladdr}` reads back.* Each
$`\mathsf{globaladdr}~s~N` reads back from its attribute, its empty operand
types and its result type, and an op that decodes from attributes and
types is a $`\mathsf{globaladdr}` whose own attribute and types they are.
:::
