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

:::moduleDocs (fingerprint := "9415480017361798480")
:::

:::readable Fir.readItems_reads (pin := Fir.Text.readItems) (pin := Fir.Item.tokens) (pin := Fir.Func.types) (fingerprint := "2526066823815534157")
*Theorem: a module's items read back.* For every dialect with a
{ref "The-fir-specification--Text-format--Grammar"}[text format] and every
list of items such that, for the function $`f` of each item,
$`\mathrm{tyattr}(t)` is written as a type for each type $`t` of
$`\mathrm{types}(f)`, every type that the text of $`f` states, the
reader of the items of a module
{ref "The-fir-specification--Text-format--The-grammar-step"}[reads] the
tokens of the items, one after the other, as their trees before the word
`locs`, up to positions. At the top of a module that word starts the
location table and stops the reader of items.
:::

:::readable Fir.readModule_tokens (pin := Fir.Text.readModule) (pin := Fir.Module.tokens) (pin := Fir.Module.funcs) (pin := Fir.Func.types) (pin := Fir.LocTable.InLimits) (fingerprint := "13685553452659558979")
*Theorem: the grammar step reads a module's tokens as its tree.* For every
dialect with a text format and every
module $`m` such that:

* for each function $`f` of $`m` and each type $`t` of
  $`\mathrm{types}(f)`, $`\mathrm{tyattr}(t)` is written as a type, and
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
step of the round trip. Of all the readers, only the readers of types and
of lines and columns reject a token of the right kind, and the two
conditions cover them. Being within limits also bounds the location
references, which no reader checks.
:::

:::readable Fir.Module.WellFormed.readModule_tokens (pin := Fir.Module.WellFormed) (pin := Fir.Func.WellFormed) (fingerprint := "12684728694162639599")
*Theorem: the grammar step for a well-formed module.* For every dialect
with signatures and a text format, every
{ref "The-fir-specification--Text-format--Round-trips"}[well-formed]
module $`m` and all tokens $`\mathit{ts}` that hold the tokens of $`m` and
then $`\mathsf{eof}`, at any positions, the reader of a module gives a tree
that erases to the tree of $`m`. A well-formed module writes each type as a
type, and its location table is
{ref "The-fir-specification--Abstract-syntax--Locations"}[within limits].
:::

:::readable Fir.Module.WellFormed.read_print (pin := Fir.Text.lex) (pin := Fir.Module.print) (fingerprint := "10943986515388161621")
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

:::readable Fir.Module.Valid.read_print (pin := Fir.Module.Valid) (fingerprint := "14595993799706723983")
*Theorem: the first two steps read a valid module's text as its tree.* For
every dialect with signatures, validation rules and a text format whose
text is {ref "The-fir-specification--Text-format--Grammar"}[lawful], and
every {ref "The-fir-specification--Validation--The-general-rules"}[valid]
module $`m`, the lexer reads the printed text of $`m` as some tokens, and
the reader of a module reads those tokens as a tree that erases to the tree
of $`m`. Every valid module of such a dialect is
{ref "The-fir-specification--Text-format--Round-trips"}[well formed].
:::
