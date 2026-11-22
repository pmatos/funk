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

:::moduleDocs (fingerprint := "17156832367123220430")
:::

:::readable Fir.nil_of_map_erase Fir.plainHeader_eq (pin := Fir.Text.plainHeader) (fingerprint := "11566037241645585007")
*Lemmas: a header with no signature attributes is plain.* Lists of
attributes that erase to empty lists are empty. So the header of an item
whose parameters and results carry no attributes and whose parameters do
not end in `...` is plain, at any positions.
:::

:::readable Fir.isDialectWord_ne Fir.DialectItem.WellFormed.decodeItem_eq (pin := Fir.Text.decodeDialectItem) (pin := Fir.DialectItem.WellFormed) (fingerprint := "8799817166015756634")
*Theorems: an item of a dialect's kind decodes back.* A word of a dialect
holds a `.`, so it is neither `func`, `module`, `aggregate`, `global` nor
`extern`.
For every dialect with
a text format and every well-formed item $`i` of a dialect's kind, an item
as written that erases to the tree of $`i` decodes as $`i`, at any
positions: its kind is a word of a dialect, its body is no blocks, its
result types and its parameters decode back, and its attributes are kept
as they were read.
:::

:::readable Fir.decodeFields_eq Fir.Aggregate.WellFormed.decodeItem_eq (pin := Fir.Text.decodeAggregate) (pin := Fir.Aggregate.WellFormed) (fingerprint := "2187614322805128002")
*Theorems: an aggregate's layout decodes back.* Fields whose numbers are
within the limit and whose types are written as types and decode back
decode back from the attributes they write, at any positions. So for every
dialect with a text format and every well-formed aggregate's layout $`A`,
an item as written that erases to the tree of $`A` decodes as $`A`: its
kind is `aggregate`, it has no parameters or results, its body is no
blocks, and its memory, size, alignment and fields decode back.
:::

:::readable Fir.Item.WellFormed.decodeItem_eq Fir.Item.WellFormed.decodeItems_eq Fir.Global.decodeItem_eq (pin := Fir.Text.decodeItem) (pin := Fir.Text.decodeItems) (fingerprint := "7882002688714175266")
*Theorems: items decode back.* For every dialect with signatures,
validation rules and a lawful text:

* for every well-formed item, an item as written that erases to its tree
  decodes as that item;
* for every list of well-formed items, items as written that erase, in
  order, to their trees decode, one after the other, as those items.

An item that erases to the tree of a function, or of an external
declaration, decodes back by the theorems of the previous section. An item
that erases to the tree of a nested module is a `module` with no parameters, results
or attributes; its body is no blocks when the module has no dialect set and
no items, and otherwise its dialect set and items that erase to the trees
of its items, which decode back in turn. An item that erases to the tree of
an item of a dialect's kind, or of an aggregate's layout, decodes back by
the theorems above, and one that erases to the tree of a global, a `global`
item with no parameters, results or body, decodes back as that global when
its numbers are within the limit, since its attributes read back. The last two theorems call one
another, and are proved together by induction on the items.
:::

:::readable Fir.decodeLayout_eq (pin := Fir.Text.decodeMemLayout) (fingerprint := "1330681782989961273")
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
