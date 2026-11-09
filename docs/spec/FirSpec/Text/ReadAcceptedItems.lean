import VersoManual
import Fir.Text.ReadAcceptedItems
import Fir.Text.Decode
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on accepted items, which renders
`Fir.Text.ReadAcceptedItems` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Accepted items: readable blocks" =>

:::moduleDocs (fingerprint := "690646653597719966")
:::

:::readable Fir.Text.readItems_writable (pin := Fir.Text.readItems) (pin := Fir.Text.readItem) (pin := Fir.Text.ReadsWritable) (pin := Fir.Text.SItem.Writable) (pin := Fir.Text.SBody.Writable) (pin := Fir.Text.decodeItem) (fingerprint := "16901067163233167972")
*Theorem: items as read can be written.* For every list of tokens
$`\mathit{ts}`, at the top of the module or inside the body of an item,
the {ref "The-fir-specification--Text-format--Reading-the-grammar"}[reader of items]
{ref "The-fir-specification--Text-format--What-the-grammar-accepts"}[gives],
on $`\mathit{ts}`, that each item it reads can be written: each of its
parameters can be written, each of its result types is written as a
type, and its body, when it holds blocks, can be written.

The reader of items and the reader of one item call one another, for the
items inside a body, so the proof shows what each gives, together, by
induction that follows their own recursion, as for blocks. Case by case:

* at the top of the module, the word `locs` ends the items, and nothing is
  read;
* when the next token is a word, other than `locs` at the top of the
  module, that word is an item's kind: the reader reads that item and then
  the items after it, and each of the two gives that what it reads can be
  written;
* when the next token is not a word, there is no item, and the reader
  reads nothing;
* the reader of one item reads its symbol, `(`, its parameters with the
  reader of definitions, or none, `)`, its result types after `->` with
  the reader of types, or none, its attributes, `{`, its body and `}`; a
  body that starts with a word holds items, on which the case of the
  reader of items gives that the tokens left can be written, and any other
  body holds blocks that can be written, by the theorem of the previous
  section;
* an item without its symbol is an error.

Nothing is asked of an item's kind, its symbol or its attributes: decoding
accepts only a `func` without attributes, whatever its symbol.
:::
