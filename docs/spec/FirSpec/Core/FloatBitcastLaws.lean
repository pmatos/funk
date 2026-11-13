import VersoManual
import Fir.Core.FloatBitcastLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on bit cast obligations, which renders
`Fir.Core.FloatBitcastLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Bit cast obligations: readable blocks" =>

:::moduleDocs (fingerprint := "13928821166727068288")
:::

:::readable Fir.Core.unaryStrict_bitcastValue (pin := Fir.Core.UnaryStrict) (pin := Fir.Core.bitcastValue) (fingerprint := "11718810045126875929")
*Theorem: a bit cast is strict.* For every width $`N`, the
{ref "The-fir-specification--Execution--Bit-cast-rules"}[rule] of
$`\mathsf{bitcast}` gives poison on poison, so it
{ref "The-fir-specification--Execution--Width-change-obligations"}[keeps refinement],
as the width changes do.
:::

:::readable Fir.Core.toBits_propagatesPoison Fir.Core.toBits_returnsOnDefined Fir.Core.toBits_total Fir.Core.toBits_monotone (pin := Fir.PropagatesPoison) (pin := Fir.PoisonOut) (pin := Fir.UBByOwnRules) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.bitcastValue) (fingerprint := "17593624614929701954")
*Theorem: a bit cast from a float to its bits is lawful.* For every
format $`\mathsf{float}\langle e,m \rangle`, under fir's execution rules,
the bit cast to $`\mathsf{i}N` with $`N = 1+e+m` meets every obligation of
an op that {ref "The-fir-specification--Execution--Poison-classes"}[propagates poison]:

* _Poison out_: on a poison operand, its one result is poison.
* _UB only by the op's own rules_: it is never UB, so the clause holds
  with nothing to check.
* _A result on defined operands_: on the float whose bits are all zero,
  $`+0`, it gives a result.
* _Totality and monotonicity_: it gives exactly one result on every
  operand, and that result keeps refinement, since its rule is strict.

The theorems hold at every format, even one that validation rejects: they
need nothing of $`e` and $`m`.
:::

:::readable Fir.Core.ofBits_propagatesPoison Fir.Core.ofBits_returnsOnDefined Fir.Core.ofBits_total Fir.Core.ofBits_monotone (pin := Fir.PropagatesPoison) (pin := Fir.PoisonOut) (pin := Fir.UBByOwnRules) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.bitcastValue) (fingerprint := "14973835743099009102")
*Theorem: a bit cast from bits to a float is lawful.* For every format
$`\mathsf{float}\langle e,m \rangle`, the bit cast from $`\mathsf{i}N` with
$`N = 1+e+m` to the float meets the same obligations, by the same
argument: poison out, never UB, a result on the zero vector, and exactly
one result on every operand, which keeps refinement.
:::
