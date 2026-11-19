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

:::moduleDocs (fingerprint := "7252855359924225224")
:::

:::readable Fir.Core.samples (pin := Fir.instDialectTextCoreDialect) (fingerprint := "1800874016219114821")
*Definition: the core dialect's text, and one instance of every core op.*
The functions of the
{ref "The-fir-specification--Text-format--The-core-dialect-in-text"}[previous section],
$`\mathrm{opname}`, $`\mathrm{opattrs}`, $`\mathrm{decodeop}`,
$`\mathrm{tyattr}` and $`\mathrm{decodety}`, are the core dialect's
{ref "The-fir-specification--Text-format--Grammar"}[text], so the parser
and the printer of every dialect read and write core modules. The samples
are a list of op instances that
holds each of the 49 core ops at least once, both bit casts, both conversions from integers, both conversions between formats, both conversions to integers, the pointer offset in three memories, the field address with and without an index, in three memories and of a symbol that is not a word, and $`\mathsf{alloca}` of each kind, with and without a count and an alignment, of an integer, a pointer and a float type, and $`\mathsf{load}` and $`\mathsf{store}` of an integer with
four of their orderings each, and of a pointer and of a float with three, with and without an alignment, and $`\mathsf{memcpy}` and $`\mathsf{memmove}` with two orderings each, among them, with each of the ten
predicates and each of the fourteen float predicates, at widths from 1 to
128, float constants at `f32`, `f64`, `f16` and
$`\mathsf{float}\langle 2,1 \rangle`, with and without each flag, the
fast-math flags and the reserved words among them, the remainders with
flags too, and
$`\mathsf{ret}` with and without operands. On every build, checks test
that each of them reads back from its own name, attributes and types, and
that misspellings such as `i032`, `float(8, 23)`, flags in the wrong order,
`const 1` at `i1`, `const 2147483648` at `f32` and a `ptradd` whose
result is a pointer of another memory do not. The proof for every op instance, of every width, is in the
section {ref "The-fir-specification--Text-format--The-core-dialect___s-text-is-lawful"}[The core dialect's text is lawful].
:::
