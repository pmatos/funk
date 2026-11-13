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

:::moduleDocs (fingerprint := "9018222025171826093")
:::

:::readable Fir.Core.ret_total Fir.Core.ret_monotone (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.retExit) (pin := Fir.Core.Op.exit?) (pin := Fir.instDialectDenoteCoreDialectSetM) (fingerprint := "1471280454224055981")
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

:::readable Fir.Core.unreachable_exit Fir.Core.unreachable_total Fir.Core.unreachable_monotone (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.unreachableExit) (pin := Fir.Core.Op.exit?) (pin := Fir.instDialectDenoteCoreDialectSetM) (fingerprint := "13979654105211892917")
*Theorem: $`\mathsf{unreachable}` is total and monotone.* Under fir's
execution rules, $`\mathsf{unreachable}` ends in UB and in nothing else,
and so it is
{ref "The-fir-specification--Execution--Poison-classes"}[total] and
{ref "The-fir-specification--Execution--Poison-classes"}[monotone].

By its {ref "The-fir-specification--Execution--Control-flow-rules"}[rule],
its exit on the empty operand vector, its only one, is UB:

$$`\mathrm{exit}_{\mathsf{unreachable}}() = \{ \text{UB} \}`

UB is an exit, so it has one everywhere, which is totality. UB allows
anything, so whatever the exit is on operands that refine the empty
vector, UB allows it, which is monotonicity. $`\mathsf{unreachable}` is an
exception to poison propagation, so these are the only obligations it has.
:::
