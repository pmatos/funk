import VersoManual
import Fir.Text.ReadModule
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the module read back, which renders
`Fir.Text.ReadModule` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The module read back: readable blocks" =>

:::moduleDocs (fingerprint := "500872842175542027")
:::

:::readable Fir.readDialectName_reads Fir.readDialects_reads (pin := Fir.Text.readDialectName) (pin := Fir.Text.readDialects) (pin := Fir.dialectsTokens) (fingerprint := "2049900563290384102")
*Theorems: a dialect set reads back.* The reader of a dialect's name reads
the token $`\mathsf{word}~x` as $`x`, before any token. The reader of a
dialect set reads the tokens of a set as the set, before any token but a
comma and the word `dialects`: an empty set has no tokens, and the reader
reads none, since what follows is not `dialects`; a set of names is
`dialects`, its first name, and each other name after a comma, which the
reader of a list reads until no comma follows.
:::

:::readable Fir.Item.kind Fir.Item.tokens_eq Fir.head_items Fir.Item.TypesWritable Fir.Item.TypesWritableList Fir.Item.typesWritableList_iff Fir.itemsEnd (pin := Fir.Item.tokens) (pin := Fir.Func.types) (fingerprint := "11791088928063739089")
*Definitions: an item's kind, and the types it writes.* The kind of an
item is `func` for a function and `module` for a nested module, and the
tokens of an item start with $`\mathsf{word}` of its kind. So the tokens of
a list of items, then more tokens, start with the word `func` or `module`,
or, when the list is empty, as the tokens after it do. An item writes its
types as types when, for a function $`f`, $`\mathrm{tyattr}(t)` is written
as a type for each type $`t` of $`\mathrm{types}(f)`, every type that the
text of $`f` states, and, for a nested module, when each of its items does,
at any depth. A list of items ends at the word `locs` at the top of a
module, and at `}` in the body of an item.
:::

:::readable Fir.Item.reads Fir.Item.readsList (pin := Fir.Text.readItems) (pin := Fir.Text.readItem) (pin := Fir.Item.tree) (fingerprint := "10654472399646714330")
*Theorems: an item, and a list of items, read back.* For every dialect
with a {ref "The-fir-specification--Text-format--Grammar"}[text format]:

* for every item that writes its types as types, the reader of an item
  {ref "The-fir-specification--Text-format--The-grammar-step"}[reads] its
  tokens after its kind as its tree, up to positions, before any token;
* for every list of items each of which writes its types as types, the
  reader of items reads their tokens, one after the other, as their trees,
  up to positions, before the word `locs` at the top of a module, or
  before `}` in the body of an item.

A function reads back by the theorem of the previous section. A nested
module reads back as its symbol, `(`, no parameters since `)` follows, `)`,
no results and no attributes since `{` follows, `{`, then its body: no
blocks when `}` follows, which is the tree of a module with no dialect set
and no items, and otherwise its dialect set and its items, which start with
a word, read by the reader of a dialect set and the reader of items; then
`}`. The two theorems call one another, and are proved together by
induction on the items.
:::

:::readable Fir.readModule_tokens (pin := Fir.Text.readModule) (pin := Fir.Module.tokens) (pin := Fir.Item.TypesWritable) (pin := Fir.LocTable.InLimits) (fingerprint := "1579415746721921971")
*Theorem: the grammar step reads a module's tokens as its tree.* For every
dialect with a text format and every
module $`m` such that:

* each item of $`m` writes its types as types, at any depth, and
* the location table of $`m` is
  {ref "The-fir-specification--Abstract-syntax--Locations"}[within limits],

on any tokens that hold the
{ref "The-fir-specification--Text-format--Lexing-printed-text"}[tokens of $`m`]
and then $`\mathsf{eof}`, at any positions, the reader of a module gives a
tree $`s` that
{ref "The-fir-specification--Text-format--The-tree-that-the-grammar-reads"}[erases]
to the tree of $`m`:

$$`\begin{aligned} & \mathrm{toks}(\mathit{ts}) = \mathrm{tokens}(m)~\mathsf{eof} \implies \\ & \exists\, s.\ \mathrm{readmodule}(\mathit{ts}) = \mathsf{ok}(s) \\ & \quad \wedge\ \mathrm{erase}(s) = \mathrm{tree}(m) \end{aligned}`

Here $`\mathrm{readmodule}` is the reader of a module. This is the second
step of the round trip. The reader reads the dialect set first, which an
item's `func` or `module` or the table's `locs` ends. Of all the readers,
only the readers of types and of lines and columns reject a token of the
right kind, and the two conditions cover them. Being within limits also
bounds the location references, which no reader checks.
:::

:::readable Fir.Item.WellFormed.typesWritable Fir.Item.WellFormed.typesWritableList Fir.Module.WellFormed.readModule_tokens (pin := Fir.Module.WellFormed) (pin := Fir.Func.WellFormed) (pin := Fir.Item.WellFormed) (fingerprint := "15152913429717558126")
*Theorem: the grammar step for a well-formed module.* For every dialect
with signatures and a text format, every
{ref "The-fir-specification--Text-format--Round-trips"}[well-formed]
module $`m` and all tokens $`\mathit{ts}` that hold the tokens of $`m` and
then $`\mathsf{eof}`, at any positions, the reader of a module gives a tree
that erases to the tree of $`m`. A well-formed item, and so each item of a
list of well-formed items, writes each type as a type, and the location
table of a well-formed module is
{ref "The-fir-specification--Abstract-syntax--Locations"}[within limits].
:::

:::readable Fir.Module.WellFormed.read_print (pin := Fir.Text.lex) (pin := Fir.Module.print) (fingerprint := "14501421206763944168")
*Theorem: the first two steps read a well-formed module's text as its
tree.* For every dialect with signatures and a text format and every
well-formed module $`m`, the
{ref "The-fir-specification--Text-format--The-parser"}[lexer] reads the
{ref "The-fir-specification--Text-format--The-canonical-printer"}[printed text]
of $`m` as some tokens, and the reader of a module reads those tokens as a
tree that erases to the tree of $`m`:

$$`\begin{aligned} \exists\, \mathit{ts}, s.\ & \mathrm{lex}(\mathrm{print}(m)) = \mathsf{ok}(\mathit{ts}) \\ \wedge\ & \mathrm{readmodule}(\mathit{ts}) = \mathsf{ok}(s) \\ \wedge\ & \mathrm{erase}(s) = \mathrm{tree}(m) \end{aligned}`

The {ref "The-fir-specification--Text-format--Writable-tokens"}[first step]
gives the tokens of $`m`, then $`\mathsf{eof}`, and the theorem above
reads them.
:::

:::readable Fir.Module.Valid.read_print (pin := Fir.Module.Valid) (fingerprint := "4073448004416756215")
*Theorem: the first two steps read a valid module's text as its tree.* For
every dialect with signatures, validation rules and a text format whose
text is {ref "The-fir-specification--Text-format--Grammar"}[lawful], and
every {ref "The-fir-specification--Validation--The-general-rules"}[valid]
module $`m`, the lexer reads the printed text of $`m` as some tokens, and
the reader of a module reads those tokens as a tree that erases to the tree
of $`m`. Every valid module of such a dialect is
{ref "The-fir-specification--Text-format--Round-trips"}[well formed].
:::
