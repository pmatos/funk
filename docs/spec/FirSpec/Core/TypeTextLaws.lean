import VersoManual
import Fir.Core.TypeTextLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the core types in text, which
renders `Fir.Core.TypeTextLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The core types in text are lawful: readable blocks" =>

:::moduleDocs (fingerprint := "4219413424004421706")
:::

:::readable Fir.Core.toList_int_attr (fingerprint := "2552526595169716876")
*Theorem: how the integer type is spelt.* For every width $`N`, the
characters of the word that writes $`\mathsf{i}N` are `i` followed by the
decimal digits of $`N`. The proofs below read the width back through it.
:::

:::readable Fir.Core.aliasFormat_of_floatAlias Fir.Core.floatAlias_of_aliasFormat Fir.Core.Ty.decode_alias Fir.Core.Ty.decode_float (pin := Fir.Core.floatAlias) (pin := Fir.Core.aliasFormat) (pin := Fir.Core.decodeFloat) (fingerprint := "10301018937267886543")
*Theorems: a float format and its alias name each other, and each float
spelling reads back.* For every format $`(e, m)` and word $`n`,
$`\mathrm{alias}(e, m) = n` exactly when $`\mathrm{format}(n) = (e, m)`.
So the word $`n` reads back as $`\mathsf{float}\langle e,m \rangle`. And
when $`(e, m)` has no alias and $`1 + e + m \le 16{,}777{,}215`,
$`\texttt{float}(e, m)` reads back as
$`\mathsf{float}\langle e,m \rangle`.
:::

:::readable Fir.Core.Ty.decode_ptr Fir.Core.Ty.decode_attr Fir.Core.Ty.attr_decodeFloat Fir.Core.Ty.attr_decodePtr Fir.Core.Ty.attr_decode (pin := Fir.Core.maxWidth) (pin := Fir.Core.maxMemory) (pin := Fir.Core.decodePtr) (pin := Fir.Core.Ty.Valid) (pin := Fir.Core.Ty.attr) (pin := Fir.Core.Ty.decode) (fingerprint := "7758241985654017256")
*Theorems: every valid core type reads back, and a type reads back only
from its spelling.* A core type is
{ref "The-fir-specification--Validation--Core-rules"}[valid] when it is
$`\mathsf{i}N` with $`1 \le N \le 16{,}777{,}215`, or
$`\mathsf{float}\langle e,m \rangle` with $`e \ge 2`, $`m \ge 1` and
$`1 + e + m \le 16{,}777{,}215`, or $`\mathsf{ptr}\langle N \rangle` with
$`N \le 16{,}777{,}215`. For every valid core type $`t`,
$`\mathrm{decodety}(\mathrm{tyattr}(t)) = t`: in particular
$`\mathsf{ptr}\langle N \rangle` for every memory
$`1 \le N \le 16{,}777{,}215`, written $`\texttt{ptr}(N)`. And for every attribute $`a` and type
$`t`, if $`\mathrm{decodety}(a) = t` then $`\mathrm{tyattr}(t) = a`: in
particular, a format that $`\texttt{float}(e, m)` reads back as is
written $`\texttt{float}(e, m)`, since one with an alias does not decode
from it, and a pointer type that $`\texttt{ptr}(N)` reads back as is
written $`\texttt{ptr}(N)`, since $`\texttt{ptr}(0)` does not decode.

These are the third and fourth laws of a lawful text, which the
{ref "The-fir-specification--Text-format--The-core-dialect___s-text-is-lawful"}[next section]
puts together. The first needs the width to be at most 16,777,215, since a
wider type does not read back.
:::

:::readable Fir.Core.Ty.attr_isType (pin := Fir.isWord) (fingerprint := "6590097866977232082")
*Theorem: every valid core type is written as a type.* For every valid
core type $`t`, $`\mathrm{tyattr}(t)` is written as a type: a word, as
$`\mathsf{i}N`, every alias and $`\texttt{ptr}` are, the word
$`\texttt{float}` applied to two integers, or the word $`\texttt{ptr}`
applied to one. This is the type's part of the last laws of a lawful
text.
:::
