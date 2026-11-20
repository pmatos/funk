import VersoManual
import Fir.Core.MemSetPoison
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the fill poison obligations, which
renders `Fir.Core.MemSetPoison` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Fill poison obligations: readable blocks" =>

:::moduleDocs (fingerprint := "2089767263116862518")
:::

:::readable Fir.Core.fillBits Fir.Core.setLenRule_ub_fill (pin := Fir.Core.setLenRule) (pin := Fir.Core.fillPtr) (fingerprint := "8922307283932155733")
*Theorems: poison operands are filled.* Let $`\mathrm{fillbits}(v)` be
$`v` for a defined value and zero for poison. Wherever the rule of a
defined length is UB from the memories $`S`, it is UB from $`S` on
$`\mathrm{fill}(p)`, the pointer with no provenance in place of a poison
pointer, and $`\mathrm{fillbits}(v)`: a store through a pointer with no
provenance faults, and whether a store faults depends on how many units
it writes, not on what they hold.
:::

:::readable Fir.Core.memSet_makesNoPoison Fir.Core.memSet_memPropagates Fir.Core.memSet_memReturnsOnDefined (pin := Fir.MakesNoPoison) (pin := Fir.MemPropagatesPoison) (pin := Fir.MemReturnsOnDefined) (fingerprint := "13945472770053517995")
*Theorems: a fill propagates poison.* $`\mathsf{memSet}_N~o~V~W` gives no
result, so it makes no poison, and a poison operand gives no poison
result. It meets the
{ref "The-fir-specification--Memory--Poison-obligations-with-memory"}[poison obligations with memory]:
where it is UB from $`S` on a poison operand, it is UB from $`S` on the
defined operands that put the chosen length in place of a poison length,
$`\mathrm{fill}` of a poison pointer and $`\mathrm{fillbits}` of a poison
value. And on the defined operands of a pointer with no provenance, a
zero and a length of 0 it returns, from memories inside a call.
:::
