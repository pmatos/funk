import VersoManual
import Fir.Text.LexWellFormed
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on writable tokens, which renders
`Fir.Text.LexWellFormed` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Writable tokens: readable blocks" =>

:::moduleDocs (fingerprint := "9573380394114366199")
:::

:::readable Fir.forall_mem_intercalate_of Fir.comma_writable (fingerprint := "15438348163069253873")
*Lemmas: proof plumbing.* For every test $`P` on tokens, separator $`x`
whose tokens all pass $`P`, and lists of tokens $`t_1, \dots, t_n` whose
tokens all pass $`P`, every token of $`t_1~x~t_2~\dots~x~t_n` passes
$`P`; and the token $`\texttt{,}`
{ref "The-fir-specification--Text-format--Lexing-printed-text"}[can be written]. Together they show that
a list written with commas can be written when its elements can.
:::

:::readable Fir.Attr.Writable.tokens Fir.Attr.AllWritable.tokens (pin := Fir.Attr.Writable) (pin := Fir.Attr.AllWritable) (fingerprint := "10076048675647629738")
*Theorems: an attribute that can be written has tokens that can be
written.* An
{ref "The-fir-specification--Text-format--Grammar"}[attribute can be written]
when each word it holds, its own or an application's head, at any depth,
is a word. For every attribute that can be written, every one of its
tokens can be written; and for every list of attributes that can each be
written, every token of each can be written. The two are proved together,
since an application holds a list of attributes.
:::

:::readable Fir.Attr.AllWritable.mem (fingerprint := "7578950284979742545")
*Lemma: each attribute of a list that can be written can be written.* It
turns the condition on a list into one on each of its elements.
:::

:::readable Fir.Attr.IsType.writable (pin := Fir.Attr.IsType) (fingerprint := "9361101271589670088")
*Theorem: a type is an attribute that can be written.* An attribute is
written as a type when it is a word, or a word applied to attributes, and
it can be written. So every attribute written as a type can be written:
the theorem only unfolds that definition, so that the proofs can use the
condition on a type where they need the one on an attribute.
:::

:::readable Fir.Location.tokens_writable (pin := Fir.Location.numbers) (pin := Fir.Location.refs) (pin := Fir.Location.limit) (fingerprint := "7629404678764208315")
*Theorem: a location whose numbers are in range has tokens that can be
written.* For every
{ref "The-fir-specification--Abstract-syntax--Locations"}[location]
$`\mathit{loc}` each of whose numbers, its lines and columns or its
references, is below $`2^{32}`, every token of $`\mathit{loc}` can be
written. Its words, such as `fused` and `at`, are words, and its location
references are below $`2^{32}`.
:::

:::readable Fir.LocTable.InLimits.tokens (pin := Fir.LocTable.InLimits) (pin := Fir.Location.limit) (fingerprint := "17364402634687887420")
*Theorem: a location table within the limits has tokens that can be
written.* For every location table whose keys, and the numbers of whose
locations, are all below $`2^{32}`, every token of the table can be
written.
:::

:::readable Fir.regionBlocks_of_mem (pin := Fir.Operation.regionBlocks) (pin := Fir.Region.allBlocks) (fingerprint := "15394122174651925032")
*Lemma: an op's regions hold blocks below its list.* For every dialect,
op $`o` of a list of ops, and block $`b` of the regions of $`o` at any
depth, $`b` is among the blocks of the regions of the list's ops, at any
depth. It lets the proofs below go down from a list of ops into one op.
:::

:::readable Fir.Func.WellFormed.def_tokens Fir.Func.WellFormed.defs_tokens (pin := Fir.Func.WellFormed) (pin := Fir.Func.defs) (fingerprint := "5833674688040657592")
*Theorems: the definitions of a well-formed function have tokens that can
be written.* For every dialect with
{ref "The-fir-specification--Abstract-syntax--Dialects"}[signatures] and
a {ref "The-fir-specification--Text-format--Grammar"}[text format], and
every {ref "The-fir-specification--Text-format--Round-trips"}[well-formed]
function $`f`:

* every value that $`f` defines, as a parameter, a block argument or an
  op's result, at any depth, has a definition whose tokens can be written;
* so does every list of such definitions.

A well-formed function names each value with a name and states each type
as a type that can be written.
:::

:::readable Fir.Func.WellFormed.isName_of_typeOf (pin := Fir.Func.typeOf) (fingerprint := "16634295206368681076")
*Theorem: a value of a well-formed function is a name.* For every dialect
with signatures and a text format, every well-formed function $`f`, and
every name $`x` to which $`f` gives a type, $`x` is a name: $`f` gives a
type only to the values it defines. An op's operands are such values, so
their uses can be written.
:::

:::readable Fir.Func.WellFormed.rhs_tokens Fir.Func.WellFormed.lhs_tokens (pin := Fir.Func.OpWellFormed) (fingerprint := "4877409719500594295")
*Theorems: the two halves of an op of a well-formed function have tokens
that can be written.* For every dialect with signatures and a text format,
and every well-formed function $`f`:

* for every op $`o` that is well formed in $`f`, the tokens of its name,
  attributes, operands and successors can be written. Its name is a word,
  its attributes can be written, its operands have the types its
  signature asks, so $`f` defines them, and its successors' labels and
  arguments are names;
* for every list of definitions that $`f` defines, the tokens of the
  definitions and $`\texttt{=}` can be written, or no tokens when the list
  is empty.
:::

:::readable Fir.Func.WellFormed.blocks_tokens Fir.Func.WellFormed.ops_tokens Fir.Func.WellFormed.op_tokens Fir.Func.WellFormed.regions_tokens (pin := Fir.Block.allBlocks) (pin := Fir.Func.allBlocks) (pin := Fir.Func.allOps) (pin := Fir.Operation.regionBlocks) (pin := Fir.Region.allBlocks) (pin := Fir.Func.OpWellFormed) (pin := Fir.Location.limit) (fingerprint := "3303971550985368086")
*Theorems: the blocks, ops and regions of a well-formed function have
tokens that can be written.* For every dialect with signatures and a text
format, and every well-formed function $`f`:

* every list of blocks whose blocks, at any depth, are blocks of $`f` has
  tokens that can be written;
* every list of ops of $`f` whose results $`f` defines, and the blocks of
  whose regions, at any depth, are blocks of $`f`, has tokens that can be
  written;
* so does every single op of $`f` whose results $`f` defines and the
  blocks of whose regions are blocks of $`f`;
* every list of regions whose blocks, at any depth, are blocks of $`f`,
  and each of which names its kind, if any, by a word, has tokens that can
  be written.

They are proved together, since ops hold regions, which hold blocks of
ops. An op's location reference is below $`2^{32}`, since the op is well
formed, and the kinds of its regions are words, since $`f` is.
:::

:::readable Fir.Func.WellFormed.tokens (pin := Fir.Func.WellFormed) (fingerprint := "1421354120040587777")
*Theorem: a well-formed function has tokens that can be written.* For
every dialect with signatures and a text format, every token of every
well-formed function can be written: `func`, its symbol, its parameters,
its result types, which are written as types, and its blocks.
:::

:::readable Fir.dialectsTokens_writable Fir.Item.WellFormed.tokens Fir.Item.WellFormed.tokensList Fir.Module.WellFormed.tokens_writable (pin := Fir.Module.WellFormed) (pin := Fir.Item.WellFormed) (fingerprint := "8087633961352507208")
*Theorems: well-formed items and modules have tokens that can be written.*
For every dialect with signatures and a text format:

* every token of a dialect set whose names are words can be written;
* every token of a well-formed item can be written, and so can every token
  of a list of well-formed items: a function by the theorem above, and a
  nested module since its dialect set names words and its items are well
  formed, at any depth;
* every token of every well-formed module can be written. A well-formed
  module names its dialects by words, has well-formed items, and has a
  location table within the limits.
:::

:::readable Fir.Module.WellFormed.lex_print (fingerprint := "8613579067497501645")
*Theorem: the printed text of a well-formed module lexes to its tokens.*
For every dialect with signatures and a text format, and every
well-formed module $`m`, the lexer reads the printed text of $`m` without
error, and gives the tokens of $`m`, then $`\mathsf{eof}`, positions aside:

$$`\overline{\mathrm{lex}(\mathrm{print}(m))} = \mathrm{tokens}(m)~\mathsf{eof}`

This is the
{ref "The-fir-specification--Text-format--Ops___-functions-and-the-module"}[lexing theorem]
with its condition met.
:::

:::readable Fir.Module.Valid.lex_print (fingerprint := "14706671611017615997")
*Theorem: the printed text of a valid module lexes to its tokens.* For
every dialect with signatures,
{ref "The-fir-specification--Validation--Scope-and-symbols"}[validation rules]
and a lawful text format, and every
{ref "The-fir-specification--Validation--The-general-rules"}[valid] module
$`m`:

$$`\overline{\mathrm{lex}(\mathrm{print}(m))} = \mathrm{tokens}(m)~\mathsf{eof}`

Every valid module of such a dialect is
{ref "The-fir-specification--Text-format--Round-trips"}[well formed], so
the previous theorem applies. The
{ref "The-fir-specification--Text-format--The-core-dialect___s-text-is-lawful"}[core dialect's text is lawful],
so this holds for every valid core module.
:::
