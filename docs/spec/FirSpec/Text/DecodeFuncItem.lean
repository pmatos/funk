import VersoManual
import Fir.Text.DecodeFuncItem
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a function's item and an external
declaration decoded back, which renders `Fir.Text.DecodeFuncItem`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "A function's item and an external declaration decoded back: readable blocks" =>

:::moduleDocs (fingerprint := "13872687532543015115")
:::

:::readable Fir.bind_eq_of (fingerprint := "12224089499088332229")
*Lemma: proof plumbing.* When a step succeeds with $`a`, that step followed
by $`k` is $`k` run on $`a`. The proofs below follow the decoder one step
at a time with it.
:::

:::readable Fir.mapM_decodeType (pin := Fir.Text.decodeType) (fingerprint := "4261371137450438094")
*Theorem: result types decode back.* For every dialect with a
{ref "The-fir-specification--Text-format--Grammar"}[text format], all
types as written $`(a_1, q_1), \dots, (a_n, q_n)` and types
$`t_1, \dots, t_n`: if $`a_i = \mathrm{tyattr}(t_i)` and
$`\mathrm{decodety}(\mathrm{tyattr}(t_i)) = t_i` for each $`i`, then
decoding each $`(a_i, q_i)` with the
{ref "The-fir-specification--Text-format--Decoding"}[decoder of types], in
order, gives $`t_1, \dots, t_n`.
:::

:::readable Fir.Func.WellFormed.decodeFunc_eq (pin := Fir.Text.decodeFunc) (pin := Fir.Func.WellFormed) (fingerprint := "2828869244362646918")
*Theorem: a well-formed function decodes back.* For every dialect with
signatures, validation rules and a text format whose text is lawful, every
{ref "The-fir-specification--Text-format--Round-trips"}[well-formed]
function $`f`, and, as written, parameters that
{ref "The-fir-specification--Text-format--The-tree-that-the-grammar-reads"}[erase]
to the trees of the parameters of $`f`, result types that are
$`\mathrm{tyattr}(t)` for each result type $`t` of $`f` at any positions,
and blocks that erase to the trees of the blocks of $`f`: decoding a
function with the symbol of $`f` from them gives $`f` without the
attributes of its signature and not variadic, which decoding the item adds
back.

The decoder decodes the result types, builds the scope with the
{ref "The-fir-specification--Text-format--The-decoding-step"}[first pass],
decodes the parameters, and decodes the blocks in that scope with the
{ref "The-fir-specification--Text-format--Blocks-and-ops-decoded-back"}[second pass];
each step succeeds with the part of $`f` that it decodes. The decoder gives
a body of the core's kind, which is the kind of a well-formed function's
body.
:::

:::readable Fir.Func.WellFormed.funcResultAttrs_eq (pin := Fir.Text.funcResultAttrs) (fingerprint := "773847395156028776")
*Theorem: a function's results' attributes decode back.* For every
well-formed function $`f`, result types as written that are
$`\mathrm{tyattr}(t)` for each result type $`t` of $`f`, attributes for
each result but the last that are, without positions, those of each result
of $`f` but the last, and item attributes that are those of the last
result of $`f`: the attributes of the results decode as those $`f` holds.
:::

:::readable Fir.Func.WellFormed.decodeItem_eq (pin := Fir.Text.decodeFuncItem) (fingerprint := "2394104078432555939")
*Theorem: a function's item decodes back.* For every dialect with
signatures, validation rules and a lawful text, and every well-formed
function $`f`, an item as written that erases to the tree of $`f` decodes as
the item that is $`f`, at any positions. Such an item is a `func` whose
signature's attributes are those of the function and whose body is blocks,
so the decoder of items takes its branch for blocks: the only branch that
printed text reaches. The attributes of its results and its function decode
back by the theorems above, and its parameters' attributes, held in the
short form, and whether it ends in `...` read back as $`f` holds them.
:::

:::readable Fir.Extern.decodeItem_eq (pin := Fir.Text.decodeExternItem) (pin := Fir.Extern.tree) (fingerprint := "9487409647583228183")
*Theorem: an external declaration decodes back.* For every dialect with
signatures, validation rules and a lawful text, and every external
declaration $`e` whose header, the function with no blocks that it writes,
is well formed, an item as written that erases to the tree of $`e` decodes
as the item that is $`e`, at any positions. Its tree is that of the
function, of kind `extern`, so its body is no blocks, the attributes of its
results decode as the function's do, and its signature decodes as the
function's, by the theorems above; its parameters' attributes and whether
it ends in `...` read back as $`e` holds them.
:::
