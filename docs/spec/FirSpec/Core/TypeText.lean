import VersoManual
import Fir.Core.TypeText
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the core types in text, which
renders `Fir.Core.TypeText` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The core types in text: readable blocks" =>

:::moduleDocs (fingerprint := "5652973016681635909")
:::

:::readable Fir.Core.floatAlias Fir.Core.aliasFormat (fingerprint := "379769461603123496")
*Definition: the aliases of float formats.* Five float formats have a name
of their own (ADR-2026-11-09-1549), and $`\mathrm{alias}(e, m)` gives it:

* $`\mathrm{alias}(5, 10)` is `f16`, IEEE binary16;
* $`\mathrm{alias}(8, 7)` is `bf16`, bfloat16;
* $`\mathrm{alias}(8, 23)` is `f32`, IEEE binary32;
* $`\mathrm{alias}(11, 52)` is `f64`, IEEE binary64;
* $`\mathrm{alias}(15, 112)` is `f128`, IEEE binary128.

Every other format has no alias. $`\mathrm{format}(n)` reads the table the
other way: the format that the alias $`n` names, if $`n` is one.
:::

:::readable Fir.Core.Ty.attr Fir.Core.decodeFloat Fir.Core.decodePtr Fir.Core.Ty.decode (pin := Fir.Core.Ty) (pin := Fir.Core.maxWidth) (pin := Fir.Core.maxMemory) (fingerprint := "17491175145666917792")
*Definition: how a core type is written, and read back.* The
{ref "The-fir-specification--Abstract-syntax--Core-types"}[integer type]
$`\mathsf{i}N` is written $`\mathrm{tyattr}(\mathsf{i}N)`, the word `i`
followed by $`N` in decimal. The pointer type of the default memory,
$`\mathsf{ptr}\langle 0 \rangle`, is written as the word `ptr`, and the
pointer type $`\mathsf{ptr}\langle N \rangle` of another memory as the
word `ptr` applied to $`N`, as `ptr(1)` (ADR-2026-11-11-1709). A float type $`\mathsf{float}\langle e,m \rangle` is
written as its alias when it has one, such as `f32`, and otherwise as the
word `float` applied to $`e` and $`m`, as `float(5, 2)`
(ADR-2026-11-11-0951).

$`\mathrm{decodety}(a)` reads a type back. It is
$`\mathsf{ptr}\langle 0 \rangle` when $`a` is the word `ptr`, and
$`\mathsf{ptr}\langle N \rangle` when $`a` is $`\texttt{ptr}(N)` with
$`1 \le N \le 16{,}777{,}215`; the Lean calls that reading `decodePtr`.
It is $`\mathsf{i}N` when $`a` is a word made of `i` and
the decimal digits of $`N`, with no leading zeros, and
$`N \le 16{,}777{,}215`, the widest width of the core dialect. It is the
float type that an alias names when $`a` is that alias. It is
$`\mathsf{float}\langle e,m \rangle` when $`a` is
$`\texttt{float}(e, m)` with $`e, m \ge 0`,
$`1 + e + m \le 16{,}777{,}215`, and no alias for the format; the Lean
calls that reading `decodeFloat`. It is undefined otherwise, so `i032`,
`u8`, `i16777216`, `f8`, `float(8, 23)`, which is written `f32`, and
`float(-1, 3)` do not decode, and neither do `ptr(0)`, which is written
`ptr`, and `ptr(-1)`. `i0`, `float(1, 1)` and `ptr(1)` decode, and
validation rejects them.
:::
