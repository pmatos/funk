import VersoManual
import Fir.Execution.TraceCallSource
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a traced call of the target, followed back, which renders
`Fir.Execution.TraceCallSource` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "A traced call of the target, followed back: readable blocks" =>

:::moduleDocs (fingerprint := "5211086765132861869")
:::

:::readable Fir.Func.TCallsAt.source Fir.Func.TCallsAt.extMonotone (pin := Fir.Func.TCallsAt) (pin := Fir.OpTracePickMonotone) (fingerprint := "1537675644598892946")
*Theorems: a traced call of the target is one of the source.* Let the
operands $`\vec{v}` refine $`\vec{v}'`, the traced state $`s` refine
$`s'`, the module $`M'` call each symbol that $`M` can call, and the rule
of the op be monotone in the traced layer when its callee is picked. A
call of the op in $`M'` on $`\vec{v}'` from $`s'` to a symbol, after the
acts $`t_0'`, is a call in $`M` on $`\vec{v}` from $`s` to the same symbol
with the same steps, on arguments that the target's refine, after acts
that the target's refine one by one, from a traced state that the
target's refines; or the source's rule is UB after acts that the target's
first show, refined. When the
external-call rule is monotone at the symbol and types of each op that
names its callee, and at every symbol for the types of each op that picks
it, it is monotone at the symbol and types of every call of the op.
:::
