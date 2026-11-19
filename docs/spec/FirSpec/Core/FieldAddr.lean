import VersoManual
import Fir.Core.FieldAddr
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on field address rules, which renders
`Fir.Core.FieldAddr` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Field address rules: readable blocks" =>

:::moduleDocs (fingerprint := "16923402170189853415")
:::

:::readable Fir.Core.fieldOffset (pin := Fir.LayoutPlace) (pin := Fir.FieldPlace) (fingerprint := "1637129964727855705")
*Definition: the offset of a field's element.* For a layout $`l` that a
run gives, as the
{ref "The-fir-specification--Memory--The-items-a-run-gives-each-op"}[items]
place it, a field number $`j` and an integer $`k`:

$$`\mathrm{off}(l, j, k) = o_j + s_j \cdot k`

where $`o_j` is the offset of the field $`j` of $`l` and $`s_j` the units
from one of its elements to the next. When the run gives no layout, or the
layout has no field $`j`, $`\mathrm{off}(l, j, k) = 0`.
:::

:::readable Fir.Core.fieldAddrValue Fir.Core.elemAddrValue (pin := Fir.Core.movePointer) (fingerprint := "16911647874396956026")
*Definitions: the rules of $`\mathsf{fieldaddr}`.* For every pointer $`p`
and $`k \in \mathbb{B}^W`:

$$`\mathsf{fieldaddr}_{l,j}(p) = \mathrm{move}(p, \mathrm{off}(l, j, 0))`

$$`\mathsf{fieldaddr}_{l,j}(p, k) = \mathrm{move}(p, \mathrm{off}(l, j, \mathrm{signed}(k)))`

and either gives $`\mathsf{poison}` when an operand is $`\mathsf{poison}`.
The move is
{ref "The-fir-specification--Execution--Pointer-offset-rules"}[$`\mathsf{ptradd}`'s]:
it keeps the pointer's provenance, and the result may leave its
allocation, so the rule is never UB.
:::

:::readable Fir.Core.fieldAddrResult (fingerprint := "4875547781883285764")
*Definition: the result of $`\mathsf{fieldaddr}`.* On its operands, the
one result of $`\mathsf{fieldaddr}~s~j~N~w` in the layout $`l` is the
field's address when $`w` is none, and the element's address when it
takes an index.
:::
