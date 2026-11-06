import VersoManual
import Fir.Core.ControlLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on control-flow obligations, which
renders `Fir.Core.ControlLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Control-flow obligations: readable blocks" =>

:::readable Fir.Core.ret_total Fir.Core.ret_monotone (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.retExit) (pin := Fir.Core.Op.exit?) (pin := Fir.instDialectDenoteCoreDialectSetM) (fingerprint := "8075508603752795612")
*Theorem: $`\mathsf{ret}` is total and monotone.* For every list of
result types $`t^*`, under fir's execution rules, $`\mathsf{ret}~t^*` is
{ref "The-fir-specification--Execution--Poison-classes"}[total] and
{ref "The-fir-specification--Execution--Poison-classes"}[monotone].

$`\mathsf{ret}` is a terminator, so both obligations look at its exit,
where it sends control. By its
{ref "The-fir-specification--Execution--Control-flow-rules"}[rule], it
sends control back to the caller on every operand vector, poison or not:

$$`\mathrm{exit}_{\mathsf{ret}~t^*}(\vec{v}) = \{ \mathsf{ok}~\mathsf{ret} \}`

So it has an exit everywhere, which is totality, and the same exit on
operands that refine others, which is all that monotonicity asks of a
terminator. The values it returns are its operands, which the interpreter
passes on as they are, so refining them refines what the caller gets.
$`\mathsf{ret}` is an exception to poison propagation, so these are the
only obligations it has.
:::
