import VersoManual
import Fir.Core.Control
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on control-flow rules, which renders
`Fir.Core.Control` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Control-flow rules: readable blocks" =>

:::moduleDocs (fingerprint := "7677257559967342185")
:::

:::readable Fir.Core.retExit (pin := Fir.Exit) (fingerprint := "1168687934119480536")
*Definition: the rule of $`\mathsf{ret}`.* $`\mathsf{ret}` sends control
back to the caller, whatever its operands:

$$`\mathrm{exit}_{\mathsf{ret}}(v_1, \dots, v_n) = \mathsf{ret}`

Here $`\mathrm{exit}_o` is
{ref "The-fir-specification--Execution--Effects-and-op-semantics"}[where control goes]
when the terminator $`o` ends its block, and $`\mathsf{ret}` on the right
says: return from the function. The
{ref "The-fir-specification--Execution--The-interpreter"}[interpreter] then
returns the operands $`v_1, \dots, v_n` as they are, any number of them
(ADR-2026-10-29-2008), poison included: $`\mathsf{ret}` is an exception to
poison propagation that passes values on (ADR-2026-10-29-2006). It is never
UB.
:::

:::readable Fir.Core.unreachableExit (pin := Fir.Exit) (pin := Fir.Ev) (fingerprint := "8832329122222010874")
*Definition: the rule of $`\mathsf{unreachable}`.* $`\mathsf{unreachable}`
has no operands and no successors, and reaching it is immediate UB, with
the reason `unreachable reached` (ADR-2026-11-09-1548):

$$`\mathrm{exit}_{\mathsf{unreachable}}() = \text{UB}`

A producer puts $`\mathsf{unreachable}` where it knows control never goes,
such as after a call that never returns. Since a run that reaches it is UB,
a compiler may assume that no run does, and may delete the code that only
leads to it. It is an exception to poison propagation that is always UB,
which the
{ref "The-fir-specification--Execution--Poison-classes"}[poison classes]
allow (ADR-2026-10-29-2006).
:::
