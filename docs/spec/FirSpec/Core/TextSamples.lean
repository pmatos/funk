import VersoManual
import Fir.Core.TextSamples
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the samples of the core dialect's
text, which renders `Fir.Core.TextSamples` (ADR-2026-11-05-2012). Each
block explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "The core dialect's text, checked: readable blocks" =>

:::moduleDocs (fingerprint := "753050731480953766")
:::

:::readable Fir.Core.samples (pin := Fir.instDialectTextCoreDialect) (fingerprint := "4554056366472945291")
*Definition: the core dialect's text, and one instance of every core op.*
The functions of the
{ref "The-fir-specification--Text-format--The-core-dialect-in-text"}[previous section],
$`\mathrm{opname}`, $`\mathrm{opattrs}`, $`\mathrm{decodeop}`,
$`\mathrm{tyattr}` and $`\mathrm{decodety}`, are the core dialect's
{ref "The-fir-specification--Text-format--Grammar"}[text], so the parser
and the printer of every dialect read and write core modules. The samples
are a list of op instances that
holds each of the 38 core ops at least once, both bit casts, both conversions from integers, both conversions between formats and the pointer offset in three memories among them, with each of the ten
predicates and each of the fourteen float predicates, at widths from 1 to
128, float constants at `f32`, `f64`, `f16` and
$`\mathsf{float}\langle 2,1 \rangle`, with and without each flag, and
$`\mathsf{ret}` with and without operands. On every build, checks test
that each of them reads back from its own name, attributes and types, and
that misspellings such as `i032`, `float(8, 23)`, flags in the wrong order,
`const 1` at `i1`, `const 2147483648` at `f32` and a `ptradd` whose
result is a pointer of another memory do not. The proof for every op instance, of every width, is in the
section {ref "The-fir-specification--Text-format--The-core-dialect___s-text-is-lawful"}[The core dialect's text is lawful].
:::
