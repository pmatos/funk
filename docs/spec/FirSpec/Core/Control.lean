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
(ADR-2026-10-30-0816), poison included: $`\mathsf{ret}` is an exception to
poison propagation that passes values on (ADR-2026-10-30-0818). It is never
UB.
:::
