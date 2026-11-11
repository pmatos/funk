import VersoManual
import Fir.Text.DecodeModule
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the module decoded back, which
renders `Fir.Text.DecodeModule` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The module decoded back: readable blocks" =>

:::moduleDocs (fingerprint := "7958503940249937813")
:::

:::readable Fir.bind_eq_of (fingerprint := "12224089499088332229")
*Lemma: proof plumbing.* When a step succeeds with $`a`, that step followed
by $`k` is $`k` run on $`a`. The proofs below follow the decoder one step
at a time with it.
:::

:::readable Fir.mapM_decodeType (pin := Fir.Text.decodeType) (fingerprint := "10737967661857746415")
*Theorem: result types decode back.* For every dialect with a
{ref "The-fir-specification--Text-format--Grammar"}[text format], all
types as written $`(a_1, q_1), \dots, (a_n, q_n)` and types
$`t_1, \dots, t_n`: if $`a_i = \mathrm{tyattr}(t_i)` and
$`\mathrm{decodety}(\mathrm{tyattr}(t_i)) = t_i` for each $`i`, then
decoding each $`(a_i, q_i)` with the
{ref "The-fir-specification--Text-format--Decoding"}[decoder of types], in
order, gives $`t_1, \dots, t_n`.
:::

:::readable Fir.Func.WellFormed.decodeFunc_eq (pin := Fir.Text.decodeFunc) (pin := Fir.Func.WellFormed) (fingerprint := "9625755100788047290")
*Theorem: a well-formed function decodes back.* For every dialect with
signatures, validation rules and a text format whose text is lawful, every
{ref "The-fir-specification--Text-format--Round-trips"}[well-formed]
function $`f`, and, as written, parameters that
{ref "The-fir-specification--Text-format--The-tree-that-the-grammar-reads"}[erase]
to the trees of the parameters of $`f`, result types that are
$`\mathrm{tyattr}(t)` for each result type $`t` of $`f` at any positions,
and blocks that erase to the trees of the blocks of $`f`: decoding a
function with the symbol of $`f` from them gives $`f`.

The decoder decodes the result types, builds the scope with the
{ref "The-fir-specification--Text-format--The-decoding-step"}[first pass],
decodes the parameters, and decodes the blocks in that scope with the
{ref "The-fir-specification--Text-format--Blocks-and-ops-decoded-back"}[second pass];
each step succeeds with the part of $`f` that it decodes. The decoder gives
a body of the core's kind, which is the kind of a well-formed function's
body.
:::

:::readable Fir.isDialectWord_ne Fir.DialectItem.WellFormed.decodeItem_eq (pin := Fir.Text.decodeDialectItem) (pin := Fir.DialectItem.WellFormed) (fingerprint := "3870543999219301537")
*Theorems: an item of a dialect's kind decodes back.* A word of a dialect
holds a `.`, so it is neither `func` nor `module`. For every dialect with
a text format and every well-formed item $`i` of a dialect's kind, an item
as written that erases to the tree of $`i` decodes as $`i`, at any
positions: its kind is a word of a dialect, its body is no blocks, its
result types and its parameters decode back, and its attributes are kept
as they were read.
:::

:::readable Fir.Func.WellFormed.decodeItem_eq Fir.Item.WellFormed.decodeItem_eq Fir.Item.WellFormed.decodeItems_eq (pin := Fir.Text.decodeItem) (pin := Fir.Text.decodeItems) (fingerprint := "1750046234271386164")
*Theorems: items decode back.* For every dialect with signatures,
validation rules and a lawful text:

* for every well-formed function $`f`, an item as written that erases to
  the tree of $`f` decodes as the item that is $`f`;
* for every well-formed item, an item as written that erases to its tree
  decodes as that item;
* for every list of well-formed items, items as written that erase, in
  order, to their trees decode, one after the other, as those items.

An item that erases to the tree of a function is a `func` with no
attributes and a body of blocks, so the decoder of items takes its branch
for blocks: the only branch that printed text reaches. An item that erases
to the tree of a nested module is a `module` with no parameters, results
or attributes; its body is no blocks when the module has no dialect set and
no items, and otherwise its dialect set and items that erase to the trees
of its items, which decode back in turn. An item that erases to the tree of
an item of a dialect's kind decodes back by the theorem above. The last two theorems call one
another, and are proved together by induction on the items.
:::

:::readable Fir.Module.WellFormed.decodeModule_eq (pin := Fir.Text.decodeModule) (pin := Fir.Module.WellFormed) (fingerprint := "4661324548460288479")
*Theorem: the decoding step gives a well-formed module back from its
tree.* For every dialect with signatures, validation
rules and a text format whose text is
{ref "The-fir-specification--Text-format--Grammar"}[lawful], every
well-formed module $`m` and every module as written $`s` that erases to
the tree of $`m`, decoding $`s` gives $`m`:

$$`\begin{aligned} & \mathrm{erase}(s) = \mathrm{tree}(m) \implies \\ & \quad \mathrm{decodemodule}(s) = \mathsf{ok}(m) \end{aligned}`

Here $`\mathrm{decodemodule}` is the decoder of a module. This is the
third step of the round trip. Decoding reads positions only to
report errors, and on such a tree it reports none, so the positions of
$`s` do not matter.
:::
