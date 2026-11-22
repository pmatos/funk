import VersoManual
import Fir.Syntax.FuncAttrs
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a signature's attributes, which
renders `Fir.Syntax.FuncAttrs` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "A signature's attributes: readable blocks" =>

:::moduleDocs (fingerprint := "11258007099659161380")
:::

:::readable Fir.padAttrs Fir.trimAttrs Fir.AttrsTrimmed Fir.Func.paramAttrsAll Fir.Func.resultAttrsAll (fingerprint := "9438147280391856958")
*Definitions: the attributes of each place.* A function holds lists of
attributes for its parameters, or its results, its places, in a short
form: one list for each of the first places, and none for the rest, with
no empty list at the end.

* $`\mathrm{pad}_n(A)` gives the attributes of each of $`n` places: the
  $`i`th list of $`A`, or the empty list when $`A` has none at $`i`.
* $`\mathrm{trim}(A)` leaves out the empty lists at the end of $`A`.
* $`A` has the form a function holds for $`n` places when it has at most
  $`n` lists and its last list, if any, is not empty. Whether it does can
  be decided.
* The attributes of each parameter of a function $`f` are
  $`\mathrm{pad}_{|\mathsf{params}|}(\mathsf{paramAttrs})`, and those of
  each result $`\mathrm{pad}_{|\mathsf{results}|}(\mathsf{resultAttrs})`.

The text writes the attributes of every place, and decoding gives back
the short form, so a function has one tree, and one text. The attributes
come after a type, as in the core's extension markers in
`func @f(%c: i8 sext) -> i8 zext`. The dialect of each type says which it
allows, and a function whose parameters end in `...` is not valid: only an
external declaration may be variadic.
:::

:::readable Fir.Extern.func (fingerprint := "17810137597958032041")
*Definition: the function whose header a declaration writes.* An
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[external declaration]
$`e` writes the header of a function: $`\mathrm{func}(e)` has the symbol,
the parameters, the results, the attributes and the `...` of $`e`, and a
body of the core's kind with no blocks. The text of $`e`, its tree and its
round trip are those of $`\mathrm{func}(e)`, with the kind `extern` in
place of `func`, and the attributes of each of its places are those of
$`\mathrm{func}(e)`.
:::
