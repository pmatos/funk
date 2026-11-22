import VersoManual
import Fir.Text.DecodeAcceptedModule
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on what decoding accepts, which renders
`Fir.Text.DecodeAcceptedModule` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "What decoding accepts: readable blocks" =>

:::moduleDocs (fingerprint := "7105025194281100541")
:::

:::readable Fir.decodeDialectItem_wellFormed (pin := Fir.Text.decodeDialectItem) (pin := Fir.DialectItem.WellFormed) (fingerprint := "14159535660974727433")
*Theorems: an item of a dialect's kind decoded from a tree that can be
written is well formed.* For every dialect with a text format, whose text is lawful, and
every item as read whose kind is a word of a dialect, whose parameters can
be written, whose result types are written as types and whose attributes
can be written: when it decodes as an item of a dialect's kind, that item
is well formed. Its body is then empty, its types decoded from attributes
written as types, and its attributes kept as they were read.
:::

:::readable Fir.decodeFields_wellFormed Fir.decodeAggregate_wellFormed (pin := Fir.Text.decodeAggregate) (pin := Fir.Aggregate.WellFormed) (fingerprint := "5346658473864176252")
*Theorems: an aggregate's layout as decoded is well formed.* For a
dialect whose text is lawful, fields decoded from attributes that can be
written have their numbers within the limit, and their types are written
as types and decode back. So an aggregate's layout decoded from
attributes that can be written is well formed.
:::

:::readable Fir.decodeItem_wellFormed Fir.decodeItems_wellFormed Fir.decodeGlobal_wellFormed (pin := Fir.Text.decodeItem) (pin := Fir.Text.decodeItems) (pin := Fir.Text.SItem.Writable) (fingerprint := "16888571256159249617")
*Theorems: items decoded from a tree that can be written are well formed.*
Let $`d` be a dialect with a signature, validation rules and a text, whose
text is lawful:

* for every item as read that can be written: when it decodes to an item,
  that item is well formed;
* for every list of items as read that can be written: when it decodes to
  a list of items, each of them is well formed.

A `func` and an `extern` decode by the theorems of the previous section.
A `module` decodes only when it has no parameters, results or
attributes; its body then holds no blocks, or a dialect set whose names are
words and items that can be written, which decode to well-formed items in
turn. An `aggregate`, and an item whose kind is a word of a dialect,
decode by the theorems above, and a `global` item decodes only as a global
whose attributes read, so whose numbers are within the limit. The last two theorems call one another, and are proved together by
induction on the items.
:::

:::readable Fir.decodeLayout_inLimits (pin := Fir.Text.decodeMemLayout) (fingerprint := "9574340244746265937")
*Theorem: decoded entries are within the limit.* When the entries of a data
layout as written decode, each entry they decode to is within the limit.
:::

:::readable Fir.decodeModule_wellFormed (pin := Fir.Text.decodeModule) (pin := Fir.Module.WellFormed) (pin := Fir.Text.SModule.Writable) (fingerprint := "14496348441520802811")
*Theorem: the decoding step.* Let $`d` be a dialect with a signature,
validation rules and a text, whose text is lawful. For every module $`s`
as read that can be written, and every module $`m` of $`d`: when $`s`
{ref "The-fir-specification--Text-format--Decoding"}[decodes] to $`m`,
$`m` is well formed:

$$`\begin{aligned} & s \text{ can be written} \\ & \wedge\ \mathrm{decodemodule}(s) = \mathsf{ok}(m) \\ & \quad \implies m \text{ is well formed} \end{aligned}`

Here $`\mathrm{decodemodule}(s) = \mathsf{ok}(m)` says that $`s` decodes
to $`m` without an error. Each item of $`m` is decoded from an item of
$`s`, so it is well formed; each entry of the layout of $`m` decodes, so
its numbers are within the limit; and $`m` keeps the dialect set of $`s`,
whose names are words, and its location table, which is within the limits.
These are the four conditions of a well-formed module. This is the last of the
parser's three steps.
:::
