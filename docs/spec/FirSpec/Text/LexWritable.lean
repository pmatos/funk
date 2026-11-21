import VersoManual
import Fir.Text.LexWritable
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on tokens that can be written, which renders
`Fir.Text.LexWritable` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Tokens that can be written: readable blocks" =>

:::moduleDocs (fingerprint := "10356277631743366943")
:::

:::readable Fir.forall_mem_intercalate_of Fir.comma_writable (fingerprint := "15438348163069253873")
*Lemmas: proof plumbing.* For every test $`P` on tokens, separator $`x`
whose tokens all pass $`P`, and lists of tokens $`t_1, \dots, t_n` whose
tokens all pass $`P`, every token of $`t_1~x~t_2~\dots~x~t_n` passes
$`P`; and the token $`\texttt{,}`
{ref "The-fir-specification--Text-format--Lexing-printed-text"}[can be written]. Together they show that
a list written with commas can be written when its elements can.
:::

:::readable Fir.Attr.Writable.tokens Fir.Attr.AllWritable.tokens (pin := Fir.Attr.Writable) (pin := Fir.Attr.AllWritable) (fingerprint := "2842475737533523099")
*Theorems: an attribute that can be written has tokens that can be
written.* An
{ref "The-fir-specification--Text-format--Grammar"}[attribute can be written]
when each word it holds, its own or an application's head, at any depth,
is a word, and each float literal it holds can be written: a decimal's
fraction is one or more decimal digits, and hexadecimal bits are one or
more lowercase hexadecimal digits. For every attribute that can be written, every one of its
tokens can be written; and for every list of attributes that can each be
written, every token of each can be written. The two are proved together,
since an application holds a list of attributes.
:::

:::readable Fir.Attr.AllWritable.mem (fingerprint := "7578950284979742545")
*Lemma: each attribute of a list that can be written can be written.* It
turns the condition on a list into one on each of its elements.
:::

:::readable Fir.Attr.AllWritable.of_mem (fingerprint := "15356391788914094031")
*Theorem: a list of attributes that can each be written can be written.*
:::

:::readable Fir.Attr.IsType.writable (pin := Fir.Attr.IsType) (fingerprint := "13149683016674199934")
*Theorem: a type is an attribute that can be written.* An attribute is
written as a type when it is a word, or a word applied to attributes, and
it can be written. So every attribute written as a type can be written:
the theorem only unfolds that definition, so that the proofs can use the
condition on a type where they need the one on an attribute.
:::

:::readable Fir.Func.paramsTokens_writable Fir.Func.resultsTokens_writable (pin := Fir.Func.paramsTokens) (pin := Fir.Func.resultsTokens) (fingerprint := "6030827737250491798")
*Theorems: a function's signature has tokens that can be written.* For
every dialect with a {ref "The-fir-specification--Text-format--Grammar"}[text format]
and every function $`f`:

* when the tokens of each parameter's definition can be written and each
  parameter's attributes can be written, every token of the parameters of
  $`f` can be written: the definitions and attributes, the commas, and
  `...` when $`f` is variadic;
* when each result type of $`f` is written as a type and each result's
  attributes can be written, every token of its results can be written:
  `->`, the types and attributes, and the commas.
:::
