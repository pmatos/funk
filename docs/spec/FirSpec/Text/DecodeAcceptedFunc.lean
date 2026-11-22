import VersoManual
import Fir.Text.DecodeAcceptedFunc
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a function and an external
declaration as decoded, which renders `Fir.Text.DecodeAcceptedFunc`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "A function and an external declaration as decoded: readable blocks" =>

:::moduleDocs (fingerprint := "8772201697031895531")
:::

:::readable Fir.mapM_decodeType_writable (pin := Fir.Text.decodeType) (fingerprint := "13728904447647436187")
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

:::readable Fir.decodeFunc_wellFormed (pin := Fir.Text.decodeFunc) (pin := Fir.Func.WellFormed) (pin := Fir.Func.typeOf) (pin := Fir.Func.defs) (pin := Fir.Func.types) (fingerprint := "12717166577573691148")
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

:::readable Fir.decodeFunc_lengths Fir.Func.WellFormed.withAttrs Fir.Attr.allWritable_of_mem Fir.funcResultAttrs_wellFormed (pin := Fir.Text.funcResultAttrs) (pin := Fir.AttrsTrimmed) (fingerprint := "16348431447767716566")
*Lemmas: a decoded function's signature.* For every dialect with a
signature, validation rules and a text:

* a function that the decoder gives has one parameter for each definition
  read, and one result for each type read;
* a well-formed function stays well formed with any attributes for its
  parameters and results that are in the short form, at most one list per
  place and none empty at the end, and can be written, and whether or not
  its parameters end in `...`;
* attributes that can each be written can all be written;
* when the attributes of a `func`'s results decode, from a list of
  attributes for each result but the last that can be written and the
  item's attributes, which can be written, they are in the short form for
  its results, and can be written.
:::

:::readable Fir.decodeFuncItem_wellFormed (pin := Fir.Text.decodeFuncItem) (pin := Fir.Text.funcBlocks) (fingerprint := "17245956541028204395")
*Theorem: a `func` decoded from a tree that can be written is well
formed.* Let $`d` be a dialect with a signature, validation rules and a
text, whose text is lawful. For every `func` as read whose parameters can
be written, with one list of attributes each, whose result types are
written as types, with one list of attributes for each but the last, whose
attributes can all be written and whose body can be written: when it
decodes to an item, that item is a well-formed function. It decodes the
attributes of its results, in the short form, then its body, which holds
blocks, which can be written, or nothing, and the function is decoded from
them, and takes the attributes of its parameters in the short form too.
:::

:::readable Fir.decodeFunc_nil_body Fir.decodeExternItem_wellFormed (pin := Fir.Text.decodeExternItem) (pin := Fir.Text.externResultAttrs) (fingerprint := "593264924524035240")
*Theorems: an external declaration decoded from a tree that can be written
is well formed.* A function decoded with no blocks has a body of the
core's kind with no blocks. So, for a dialect whose text is lawful, every
`extern` as read whose parameters can be written, with one list of
attributes each, whose result types are written as types, with one list of
attributes for each but the last, and whose attributes can all be written,
decodes, when it decodes, to an external declaration whose header is a
well-formed function: its body is empty, the attributes of its results
decode as a `func`'s do, in the short form, its signature decodes as a
function's with no blocks, which is well formed, and it takes the
attributes of its parameters in the short form too.
:::
