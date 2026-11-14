import VersoManual
import Fir.Core.AllocaText
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on stack allocation in text, which
renders `Fir.Core.AllocaText` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Stack allocation in text: readable blocks" =>

:::moduleDocs (fingerprint := "15699885614698512340")
:::

:::readable Fir.Memory.AllocKind.word Fir.Core.decodeKind Fir.Core.decodeKind_word (pin := Fir.Memory.AllocKind) (fingerprint := "10002023613266958229")
*Definition: the words of the kinds of an allocation.* The
{ref "The-fir-specification--Memory--The-memory-model"}[kinds] of an
allocation are written as the words `stack`, `global` and `heap`, and each
word reads back as the kind it writes. No other word names a kind.
:::

:::readable Fir.Core.Ty.decodeAny (pin := Fir.Core.Ty.decode) (fingerprint := "6163903026566247406")
*Definition: reading a type with no bound.* $`\mathrm{decodety}^\infty(a)`
reads a core type as
{ref "The-fir-specification--Text-format--The-core-types-in-text"}[$`\mathrm{decodety}`]
does, but with no bound on the width of $`\mathsf{i}N`, on the bits of
$`\mathsf{float}\langle e,m \rangle` in all, or on the memory of
$`\mathsf{ptr}\langle N \rangle`. $`\mathsf{alloca}` carries the type it
allocates as an attribute, and
{ref "The-fir-specification--Validation--Core-rules"}[validation], not
the text, bounds it, so every type reads back from how it is written:
`i16777216` decodes here, and validation rejects it.
:::

:::readable Fir.Core.allocaAttrs Fir.Core.decodeAlign Fir.Core.decodeAlloca (pin := Fir.Core.Ty.attr) (fingerprint := "12008250171172422689")
*Definition: how $`\mathsf{alloca}` is written, and read back.* The
attributes of $`\mathsf{alloca}_N~k~t~c~a` are, separated by spaces as
every op's attributes are (ADR-2026-11-14-0915):

$$`\mathrm{allocaattrs}(k, t, c, a) = \mathrm{word}(k)~\mathrm{tyattr}(t)~[c]~[\mathtt{align}(a)]`

where the count $`c` is written only when it is not 1, and
$`\mathtt{align}(a)` only when the op gives the alignment $`a`. Its memory
$`N` is that of its result type. So each instance has one spelling:

* `%p: ptr = alloca stack i32 @1` allocates one $`\mathsf{i32}` in memory 0;
* `%p: ptr = alloca stack i32 4 @1` allocates four;
* `%p: ptr(1) = alloca stack i8 12 align(4) @1` allocates twelve
  $`\mathsf{i8}` of memory 1, aligned to 4 units.

$`\mathrm{decodealloca}(a^*, t^*, r^*)` reads it back from no operand
types and the one result type $`\mathsf{ptr}\langle N \rangle`: from the
word of a kind $`k`, a type $`t` that
{ref "The-fir-specification--Text-format--Stack-allocation-in-text"}[$`\mathrm{decodety}^\infty`]
reads, then an integer $`c \ge 0` with $`c \ne 1` or no count, which
stands for 1, then $`\mathtt{align}(a)` with $`a \ge 0` or nothing, it is
$`\mathsf{alloca}_N~k~t~c~a`. It is undefined otherwise, so
`alloca stack i32 1`, which is written `alloca stack i32`, a negative
count, a word that names no kind, an operand and a result that is not a
pointer do not decode. `alloca heap i32`, `alloca stack i32 0` and
`alloca stack f32` decode, and validation rejects them.
:::
