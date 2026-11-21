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

:::moduleDocs (fingerprint := "3778723784203984572")
:::

:::readable Fir.bind_eq_of (fingerprint := "12224089499088332229")
*Lemma: proof plumbing.* When a step succeeds with $`a`, that step followed
by $`k` is $`k` run on $`a`. The proofs below follow the decoder one step
at a time with it.
:::

:::readable Fir.mapM_decodeType (pin := Fir.Text.decodeType) (fingerprint := "10718087776537962991")
*Theorem: result types decode back.* For every dialect with a
{ref "The-fir-specification--Text-format--Grammar"}[text format], all
types as written $`(a_1, q_1), \dots, (a_n, q_n)` and types
$`t_1, \dots, t_n`: if $`a_i = \mathrm{tyattr}(t_i)` and
$`\mathrm{decodety}(\mathrm{tyattr}(t_i)) = t_i` for each $`i`, then
decoding each $`(a_i, q_i)` with the
{ref "The-fir-specification--Text-format--Decoding"}[decoder of types], in
order, gives $`t_1, \dots, t_n`.
:::

:::readable Fir.Func.WellFormed.decodeFunc_eq (pin := Fir.Text.decodeFunc) (pin := Fir.Func.WellFormed) (fingerprint := "16531824210818449984")
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

:::readable Fir.Func.WellFormed.funcResultAttrs_eq (pin := Fir.Text.funcResultAttrs) (fingerprint := "8284754845717941051")
*Theorem: a function's results' attributes decode back.* For every
well-formed function $`f`, result types as written that are
$`\mathrm{tyattr}(t)` for each result type $`t` of $`f`, attributes for
each result but the last that are, without positions, those of each result
of $`f` but the last, and item attributes that are those of the last
result of $`f`: the attributes of the results decode as those $`f` holds.
:::

:::readable Fir.nil_of_map_erase Fir.plainHeader_eq (pin := Fir.Text.plainHeader) (fingerprint := "11598364754743841994")
*Lemmas: a header with no signature attributes is plain.* Lists of
attributes that erase to empty lists are empty. So the header of an item
whose parameters and results carry no attributes and whose parameters do
not end in `...` is plain, at any positions.
:::

:::readable Fir.isDialectWord_ne Fir.DialectItem.WellFormed.decodeItem_eq (pin := Fir.Text.decodeDialectItem) (pin := Fir.DialectItem.WellFormed) (fingerprint := "1032148435721250071")
*Theorems: an item of a dialect's kind decodes back.* A word of a dialect
holds a `.`, so it is neither `func`, `module`, `aggregate` nor `global`.
For every dialect with
a text format and every well-formed item $`i` of a dialect's kind, an item
as written that erases to the tree of $`i` decodes as $`i`, at any
positions: its kind is a word of a dialect, its body is no blocks, its
result types and its parameters decode back, and its attributes are kept
as they were read.
:::

:::readable Fir.decodeFields_eq Fir.Aggregate.WellFormed.decodeItem_eq (pin := Fir.Text.decodeAggregate) (pin := Fir.Aggregate.WellFormed) (fingerprint := "5963372079680485800")
*Theorems: an aggregate's layout decodes back.* Fields whose numbers are
within the limit and whose types are written as types and decode back
decode back from the attributes they write, at any positions. So for every
dialect with a text format and every well-formed aggregate's layout $`A`,
an item as written that erases to the tree of $`A` decodes as $`A`: its
kind is `aggregate`, it has no parameters or results, its body is no
blocks, and its memory, size, alignment and fields decode back.
:::

:::readable Fir.Func.WellFormed.decodeItem_eq Fir.Item.WellFormed.decodeItem_eq Fir.Item.WellFormed.decodeItems_eq Fir.Global.decodeItem_eq (pin := Fir.Text.decodeItem) (pin := Fir.Text.decodeItems) (fingerprint := "17725984752350504279")
*Theorems: items decode back.* For every dialect with signatures,
validation rules and a lawful text:

* for every well-formed function $`f`, an item as written that erases to
  the tree of $`f` decodes as the item that is $`f`;
* for every well-formed item, an item as written that erases to its tree
  decodes as that item;
* for every list of well-formed items, items as written that erase, in
  order, to their trees decode, one after the other, as those items.

An item that erases to the tree of a function is a `func` whose
signature's attributes are those of the function and whose body is
blocks, so the decoder of items takes its branch for blocks: the only branch that printed text reaches. An item that erases
to the tree of a nested module is a `module` with no parameters, results
or attributes; its body is no blocks when the module has no dialect set and
no items, and otherwise its dialect set and items that erase to the trees
of its items, which decode back in turn. An item that erases to the tree of
an item of a dialect's kind, or of an aggregate's layout, decodes back by
the theorems above, and one that erases to the tree of a global, a `global`
item with no parameters, results or body, decodes back as that global when
its numbers are within the limit, since its attributes read back. The last two theorems call one
another, and are proved together by induction on the items.
:::

:::readable Fir.decodeLayout_eq (pin := Fir.Text.decodeMemLayout) (fingerprint := "10099140561503703068")
*Theorem: a data layout decodes back.* For every data layout whose entries
are within the limit, and all entries as written that are, positions
aside, what its entries write, decoding them, in order, gives the layout
back.
:::

:::readable Fir.Module.WellFormed.decodeModule_eq (pin := Fir.Text.decodeModule) (pin := Fir.Module.WellFormed) (fingerprint := "1557950398911582143")
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
