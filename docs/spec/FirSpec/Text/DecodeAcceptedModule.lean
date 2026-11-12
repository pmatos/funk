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

:::moduleDocs (fingerprint := "6111608245691226456")
:::

:::readable Fir.mapM_decodeType_writable (pin := Fir.Text.decodeType) (fingerprint := "7523009022168863131")
*Lemma: result types as read decode back to themselves.* Let $`d` be a
dialect with a signature, validation rules and a text, whose text is
{ref "The-fir-specification--Text-format--Grammar"}[lawful]. For every
list of attributes, each with its position, and list of types
$`\mathit{ts}`: when the decoder of a type decodes each attribute of the
list, giving $`\mathit{ts}`, and each attribute is written as a type, then for each type $`t` of
$`\mathit{ts}`, $`\mathrm{tyattr}(t)` is written as a type and
$`\mathrm{decodety}(\mathrm{tyattr}(t)) = t`. It is the
{ref "The-fir-specification--Text-format--What-the-second-pass-accepts"}[theorem for one type],
applied to a function's result types. It is stated for any function that
gives what the decoder of a type gives on every attribute and position,
which is the same decoder written another way, so that the decoder of a
function can pass its own.
:::

:::readable Fir.decodeFunc_wellFormed (pin := Fir.Text.decodeFunc) (pin := Fir.Func.WellFormed) (pin := Fir.Func.typeOf) (pin := Fir.Func.defs) (pin := Fir.Func.types) (fingerprint := "13525234788551827041")
*Theorem: a function decoded from a tree that can be written is well
formed.* Let $`d` be a dialect with a signature, validation rules and a
text, whose text is lawful. For every symbol, list of parameters as read,
list of result types as read, each with its position, list of blocks as
read, and function $`f`: when the
{ref "The-fir-specification--Text-format--Decoding"}[decoder of a function]
gives $`f` from them, each parameter can be
{ref "The-fir-specification--Text-format--What-the-grammar-accepts"}[written],
each result type is written as a type, and the blocks can be written, then
$`f` is {ref "The-fir-specification--Text-format--Round-trips"}[well formed].

The decoder runs the first pass over the parameters and the blocks, then
the second pass over the blocks, in the scope that the first built. The
proof joins the two:

* the first pass names each value once, and its scope holds exactly the
  values that $`f` defines, in another order; so the names of $`f`'s
  values are distinct, and the scope gives each value the type
  $`\mathrm{type}_f(x)` that $`f` gives it, the type of its definition;
* the second pass gives arguments and results that can be written and read
  back, labels that are names, and ops that the scope accepts, at any
  depth;
* so each value of $`f` is a name; each label is a name; each type that
  the text of $`f` states, a result type or the type of a definition, is
  written as a type and decodes back to itself; each op of $`f`, with
  $`\mathrm{type}_f` in place of the scope, is well formed in $`f`; the
  body of $`f` is of the core's kind, as the decoder gives it; and each
  region of an op of $`f` that names a kind names it by a word.

These are the seven conditions of a well-formed function.
:::

:::readable Fir.Attr.allWritable_of_mem Fir.decodeDialectItem_wellFormed (pin := Fir.Text.decodeDialectItem) (pin := Fir.DialectItem.WellFormed) (fingerprint := "4958433398132762956")
*Theorems: an item of a dialect's kind decoded from a tree that can be
written is well formed.* Attributes that can each be written can all be
written. For every dialect with a text format, whose text is lawful, and
every item as read whose kind is a word of a dialect, whose parameters can
be written, whose result types are written as types and whose attributes
can be written: when it decodes as an item of a dialect's kind, that item
is well formed. Its body is then empty, its types decoded from attributes
written as types, and its attributes kept as they were read.
:::

:::readable Fir.decodeFuncItem_wellFormed Fir.decodeItem_wellFormed Fir.decodeItems_wellFormed (pin := Fir.Text.decodeFuncItem) (pin := Fir.Text.decodeItem) (pin := Fir.Text.decodeItems) (pin := Fir.Text.SItem.Writable) (fingerprint := "3781362611811854818")
*Theorems: items decoded from a tree that can be written are well formed.*
Let $`d` be a dialect with a signature, validation rules and a text, whose
text is lawful:

* for every `func` as read whose parameters can be written, whose result
  types are written as types and whose body can be written: when it decodes
  to an item, that item is a well-formed function;
* for every item as read that can be written: when it decodes to an item,
  that item is well formed;
* for every list of items as read that can be written: when it decodes to
  a list of items, each of them is well formed.

A `func` decodes only when it has no attributes; its body then holds
blocks, which can be written, or nothing, and the function is decoded from
them. A `module` decodes only when it has no parameters, results or
attributes; its body then holds no blocks, or a dialect set whose names are
words and items that can be written, which decode to well-formed items in
turn. An item whose kind is a word of a dialect decodes by the theorem
above. The last two theorems call one another, and are proved together by
induction on the items.
:::

:::readable Fir.decodeLayout_inLimits (pin := Fir.Text.decodeMemLayout) (fingerprint := "3187506564852275340")
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
