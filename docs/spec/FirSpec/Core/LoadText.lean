import VersoManual
import Fir.Core.LoadText
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on loads in text, which renders
`Fir.Core.LoadText` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Loads in text: readable blocks" =>

:::moduleDocs (fingerprint := "5354674448523914058")
:::

:::readable Fir.Memory.Ordering.word Fir.Core.decodeOrdering Fir.Core.decodeOrdering_word (pin := Fir.Memory.Ordering) (fingerprint := "3761968327788049239")
*Definition: the words of the orderings.* The
{ref "The-fir-specification--Memory--The-ordering-of-an-access"}[orderings]
are written as the words `nonatomic`, `unordered`, `monotonic`,
`acquire`, `release`, `acq_rel` and `seq_cst`, and each word reads back
as the ordering it writes. No other word names an ordering.
:::

:::readable Fir.Core.loadAttrs Fir.Core.decodeAccess Fir.Core.decodeLoad (pin := Fir.Core.decodeAlign) (fingerprint := "9138032434620264217")
*Definition: the text of $`\mathsf{load}`.* The attributes of
$`\mathsf{load}_N~o~W~a`, and of the loads of a pointer and of a float,
are the word of its ordering $`o`, then
$`\mathtt{align}(a)` when it gives an alignment, separated by spaces:

$$`\mathrm{loadattrs}(o, a) = \mathrm{word}(o)~[\mathtt{align}(a)]`

$`\mathrm{decodeaccess}(a^*)` reads the attributes of a load or a store
back, as an ordering and an alignment, and
$`\mathrm{decodeload}(a^*, t^*, r^*)` reads a load back: one operand of a
pointer type $`\mathsf{ptr}\langle N \rangle`, one result of an integer
type $`\mathsf{i}W`, of a pointer type $`\mathsf{ptr}\langle M \rangle`
for the load of a pointer, or of a float type
$`\mathsf{float}\langle e,m \rangle` for the load of a float, an
ordering's word, and an alignment written as
$`\mathsf{alloca}`'s is. Any other shape does not decode. So
`%v: i32 = load nonatomic %p @1` loads an $`\mathsf{i32}` at its natural
alignment, and `%v: i8 = load nonatomic align(4) %q @1` an $`\mathsf{i8}`
aligned to 4, and `%f: f32 = load nonatomic %p @1` an $`\mathsf{f32}`.
An atomic ordering and an alignment that is not a power of
two decode, and
{ref "The-fir-specification--Validation--Core-rules"}[validation] rejects
them.
:::
