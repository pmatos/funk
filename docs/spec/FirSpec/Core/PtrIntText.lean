import VersoManual
import Fir.Core.PtrIntText
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on pointers as integers in text, which
renders `Fir.Core.PtrIntText` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Pointers as integers in text: readable blocks" =>

:::moduleDocs (fingerprint := "7898506130391121134")
:::

:::readable Fir.Core.decodePtrExpose Fir.Core.decodePtrFromInt (fingerprint := "8518324523717893176")
*Definition: reading the two ops.* $`\mathsf{ptr\_expose}` decodes with no
attributes from one operand of $`\mathsf{ptr}\langle N\rangle` and one
result of $`\mathsf{i}W`, as $`\mathsf{ptrExpose}~N~W`;
$`\mathsf{ptr\_from\_int}` decodes with no attributes from one operand of
$`\mathsf{i}W` and one result of $`\mathsf{ptr}\langle N\rangle`, as
$`\mathsf{ptrFromInt}~N~W`. Any $`W` decodes: the data layout checks the
width. Every other shape does not decode.
:::

:::readable Fir.Core.decodePtrExpose_eq Fir.Core.decodePtrFromInt_eq (fingerprint := "11912856046320319969")
*Theorem: each op decodes only from its own spelling.* When
$`\mathsf{ptr\_expose}` decodes, its attributes are empty, its operands are
$`[\mathsf{ptr}\langle N\rangle]`, its results $`[\mathsf{i}W]`, and the op
is $`\mathsf{ptrExpose}~N~W`; and the same for $`\mathsf{ptr\_from\_int}`
with the operand and the result swapped. The text's laws use these to show
that the op reads back only from how it is written.
:::
