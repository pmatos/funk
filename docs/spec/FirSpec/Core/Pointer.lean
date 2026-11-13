import VersoManual
import Fir.Core.Pointer
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the pointer offset rules, which
renders `Fir.Core.Pointer` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Pointer offset rules: readable blocks" =>

:::moduleDocs (fingerprint := "10301295283553177089")
:::

:::readable Fir.Core.movePointer (pin := Fir.Memory.Pointer) (fingerprint := "237795450677840688")
*Definition: a pointer moved.* For every
{ref "The-fir-specification--Memory--The-memory-model"}[pointer] $`p`,
with provenance $`\mathrm{prov}(p)` and offset $`\mathrm{off}(p)`, and
every integer $`k`, $`\mathrm{move}(p, k)` is the pointer with the
provenance $`\mathrm{prov}(p)` and the offset $`\mathrm{off}(p) + k`. The
offset is an integer of any size: it never wraps, and it may be negative
or past the end of the allocation.
:::

:::readable Fir.Core.ptraddValue (pin := Fir.Core.movePointer) (fingerprint := "3856025442834215881")
*Definition: the rule of $`\mathsf{ptradd}`.* For every width $`W`, every
pointer $`p` and $`k \in \mathbb{B}^W`:

$$`\mathsf{ptradd}_W(p, k) = \mathrm{move}(p, \mathrm{signed}(k))`

where $`\mathrm{signed}(k)` is $`k` read in two's complement, and
$`\mathsf{ptradd}_W` gives $`\mathsf{poison}` when either operand is
$`\mathsf{poison}`. So moving the pointer at offset 3 by the
$`\mathsf{i8}` value with every bit set gives the pointer at offset 2. The
rule is never UB: only an access through the result must be in bounds.
:::
