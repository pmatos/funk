import VersoManual
import Fir.Text.SigAttrs
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the attributes of a signature, which renders
`Fir.Text.SigAttrs` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The attributes of a signature: readable blocks" =>

:::moduleDocs (fingerprint := "2398106852453540640")
:::

:::readable Fir.padAttrs_eq Fir.length_padAttrs (pin := Fir.padAttrs) (fingerprint := "15200637898841885419")
*Lemmas: the attributes of every place.* A function holds a list of
attributes for each of its first parameters, or results, and none for the
rest. For every $`n` and every list $`A` of at most $`n` lists of
attributes, the attributes of each of $`n` places,
$`\mathrm{pad}_n(A)`, are $`A` followed by $`n - |A|` empty lists; and
for every $`n` and $`A`, there are $`n` of them.
:::

:::readable Fir.trimAttrs_append_replicate Fir.trimAttrs_of_getLast (pin := Fir.trimAttrs) (fingerprint := "9064023010696768295")
*Lemmas: leaving out the empty lists at the end.* Decoding a signature
keeps the lists of attributes it reads, but the empty lists at their end,
$`\mathrm{trim}(A)`. For every list $`A` and every $`k`, the empty lists
after $`A` change nothing: $`\mathrm{trim}(A~[]^k) = \mathrm{trim}(A)`.
And a list that does not end in an empty list is its own trim.
:::

:::readable Fir.trimAttrs_padAttrs Fir.trimAttrs_trimmed (pin := Fir.AttrsTrimmed) (fingerprint := "2626984872644467821")
*Theorems: the two undo each other.* A list $`A` of lists of attributes
has the form a function holds for $`n` places when it has at most $`n`
lists and does not end in an empty one. For every such $`A`, decoding the
attributes that the text writes for each place gives $`A` back:
$`\mathrm{trim}(\mathrm{pad}_n(A)) = A`. And for every list $`A`,
$`\mathrm{trim}(A)` has that form for $`|A|` places, so what decoding
gives is a list a function can hold.
:::

:::readable Fir.dropLast_append_getLast (fingerprint := "15594925204001114533")
*Lemma: the last place apart.* For every list $`A` of lists of
attributes that is not empty, $`A` is its lists but the last, followed by
the last. Decoding reads the attributes of a function's last result apart
from the others, so the proofs join them back with it.
:::

:::readable Fir.mem_padAttrs Fir.mem_of_mem_trimAttrs Fir.mem_zip_padAttrs (fingerprint := "18081663441949473919")
*Lemmas: where each list of attributes comes from.* For every $`n` and
$`A`, each list of $`\mathrm{pad}_n(A)` is a list of $`A` or empty; each
list of $`\mathrm{trim}(A)` is a list of $`A`; and for every list $`xs` of
places and every $`A` of at most $`|xs|` lists, each list of $`A` is the
attributes of some place $`x` of $`xs`, beside it in the pairs of $`xs`
and $`\mathrm{pad}_{|xs|}(A)`.
:::
