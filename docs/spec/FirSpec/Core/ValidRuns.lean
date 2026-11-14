import VersoManual
import Fir.Core.ValidRuns
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on core functions with calls, which
renders `Fir.Core.ValidRuns` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Core functions with calls: readable blocks" =>

:::moduleDocs (fingerprint := "16257157132352493751")
:::

:::readable Fir.Core.Op.eq_call_of_callee (pin := Fir.Core.Op.callTarget?) (fingerprint := "6238840022199865495")
*Theorem: a core op that calls a function is $`\mathsf{call}` of that
function.* For every core op $`o` and symbol $`g`: if
$`\mathrm{callee}(o) = g`, then $`o` is $`\mathsf{call}~g : t^* \to r^*`
for some types $`t^*` and $`r^*`. So the rule that validation makes of
$`\mathsf{call}` applies to every op of the core dialect that calls a
function.
:::

:::readable Fir.Core.Op.total_all (pin := Fir.OpTotal) (fingerprint := "857378940163898036")
*Theorem: every core terminator and every core op with no callee that
touches no memory is total in the set monad.* For every core op $`o` that
touches no memory and is a terminator, or for which
$`\mathrm{callee}(o)` is none, $`o` is
{ref "The-fir-specification--Execution--Poison-classes"}[total]: on every
operand vector, its semantics, or its exit for a terminator, has some
outcome. These are the core ops other than $`\mathsf{call}` and
$`\mathsf{alloca}`, each total by the
{ref "The-fir-specification--Execution--Core-functions-without-calls"}[previous section].
With $`\mathsf{alloca}`, which is total with memory by
{ref "The-fir-specification--Memory--Stack-allocation-obligations"}[its own rule],
they are the ops that the progress theorem for modules asks to be total,
the ops that the interpreter runs by their own rule.
:::

:::readable Fir.Core.inModule_of_valid (pin := Fir.Func.InModule) (pin := Fir.Core.Op.Valid) (pin := Fir.Core.Op.sig) (pin := Fir.Core.Op.returnTypes) (pin := Fir.Module.context) (fingerprint := "2221359012485686113")
*Theorem: every core function valid in the context of a module runs
within that module.* Let $`M` be a core module, and $`f` a core function
{ref "The-fir-specification--Validation--The-general-rules"}[valid] in the
context $`\mathrm{ctx}(M)` of $`M`, its symbol table and the references of
its location table. Then $`f`
{ref "The-fir-specification--Execution--Progress-with-calls"}[runs within]
$`M`:

* each op of $`f` that calls a function is
  $`\mathsf{call}~g : t^* \to r^*`, and the
  {ref "The-fir-specification--Validation--Core-rules"}[core rule] of
  $`\mathsf{call}` asks that the symbol table of $`M` give $`g` the type
  $`t^* \to r^*`, the call's operand types and result types;
* $`\mathsf{br}` and $`\mathsf{cond\_br}` go only to successors they have,
  and give no results;
* $`\mathsf{ret}~t^*`, the only op whose exit returns, takes operands of
  the types $`t^*`, which the core rule of $`\mathsf{ret}` asks to be the
  result types of $`f`;
* $`\mathsf{unreachable}` neither jumps nor returns: its exit is UB, which
  ends the run.
:::
