import VersoManual
import Fir.Core.AllocaTextLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on how stack allocation reads back,
which renders `Fir.Core.AllocaTextLaws` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Stack allocation reads back: readable blocks" =>

:::moduleDocs (fingerprint := "2290677836288677683")
:::

:::readable Fir.Core.Ty.decodeAny_attr Fir.Core.Ty.attr_decodeAny (pin := Fir.Core.Ty.decodeAny) (pin := Fir.Core.Ty.attr) (fingerprint := "6038704266556441456")
*Theorems: every core type reads back with no bound, and only from its
spelling.* For every core type $`t`, valid or not,
$`\mathrm{decodety}^\infty(\mathrm{tyattr}(t)) = t`. And for every
attribute $`a`, if $`\mathrm{decodety}^\infty(a) = t`, then
$`\mathrm{tyattr}(t) = a`. So $`\mathsf{i0}`, $`\mathsf{i16777216}` and
every other type that validation rejects still reads back from how it is
written.
:::

:::readable Fir.Core.word_of_decodeKind Fir.Core.decodeAlign_toList Fir.Core.toList_of_decodeAlign (pin := Fir.Core.decodeKind) (pin := Fir.Core.decodeAlign) (fingerprint := "3475741855300332799")
*Theorems: a kind and an alignment read back only from their spelling.*
The word that names a kind is that kind's word. An alignment, none or
$`a`, reads back from how it is written, nothing or $`\mathtt{align}(a)`,
and only from it.
:::

:::readable Fir.Core.decodeAlloca_allocaAttrs Fir.Core.decodeAlloca_eq (pin := Fir.Core.decodeAlloca) (pin := Fir.Core.allocaAttrs) (fingerprint := "902851007263093324")
*Theorems: every $`\mathsf{alloca}` reads back from its spelling, and only
from it.* For every kind $`k`, type $`t`, count $`c`, alignment $`a` and
memory $`N`, valid or not:

$$`\mathrm{decodealloca}(\mathrm{allocaattrs}(k, t, c, a), \epsilon, \mathsf{ptr}\langle N \rangle) = \mathsf{alloca}_N~k~t~c~a`

And if $`\mathrm{decodealloca}(a^*, t^*, r^*) = o`, then $`o` is named
`alloca`, its attributes are $`a^*`, it has the operand types $`t^*` and
the result types $`r^*`. These are the cases of $`\mathsf{alloca}` in the
{ref "The-fir-specification--Text-format--The-core-dialect___s-text-is-lawful"}[laws of the core dialect's text].
:::

:::readable Fir.Core.Ty.attr_writable Fir.Core.allocaAttrs_writable (pin := Fir.Attr.Writable) (fingerprint := "2523899698920457991")
*Theorems: a type and the attributes of $`\mathsf{alloca}` are written as
tokens.* Every core type is written as a word or as a word applied to
integers, which the
{ref "The-fir-specification--Text-format--Tokens"}[lexer] reads as one
attribute, and so are the word of a kind, a count and
$`\mathtt{align}(a)`.
:::
