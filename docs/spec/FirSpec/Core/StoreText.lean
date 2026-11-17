import VersoManual
import Fir.Core.StoreText
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on stores in text, which renders
`Fir.Core.StoreText` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Stores in text: readable blocks" =>

:::moduleDocs (fingerprint := "13228393435064887206")
:::

:::readable Fir.Core.decodeStore (pin := Fir.Core.decodeOrdering) (pin := Fir.Core.decodeAlign) (fingerprint := "1141597553384607657")
*Definition: the text of $`\mathsf{store}`.* The attributes of
$`\mathsf{store}_N~o~W~a` are those of a load, written as
$`\mathrm{loadattrs}(o, a)`: the word of its ordering $`o`, then
$`\mathtt{align}(a)` when it gives an alignment. Its operands are the
value, then the pointer, and it has no result.
$`\mathrm{decodestore}(a^*, t^*, r^*)` reads it back: two operands, of an
integer type $`\mathsf{i}W`, or a pointer type
$`\mathsf{ptr}\langle M \rangle` for the store of a pointer, and then a
pointer type $`\mathsf{ptr}\langle N \rangle`, no result, an ordering's
word, and an
alignment written as $`\mathsf{alloca}`'s is. Any other shape does not
decode. So `store nonatomic %v, %p @1` stores an $`\mathsf{i32}` `%v` at
its natural alignment, and `store nonatomic align(4) %b, %q @1` an
$`\mathsf{i8}` `%b` aligned to 4. An atomic ordering and an alignment that
is not a power of two decode, and
{ref "The-fir-specification--Validation--Core-rules"}[validation] rejects
them.
:::
